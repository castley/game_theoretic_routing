import numpy as np
from copy import deepcopy
import random
import GS
import matplotlib.pyplot as plt
import math

diff_no_mal_msgs, step = 11, 2


class SMD(object):
    def __init__(self, no_mal_msgs, no_routes):
        """
        Class constructor.
        """
        self.no_devices = 30  # Excluding source and destination of a message
        self.no_max_devices_per_route = 10
        self.no_min_devices_per_route = 1
        self.no_mal_msgs = no_mal_msgs
        self.no_msgs = self.no_mal_msgs + 1  # we assume the last message is surveillance thus free of malware
        self.no_routes = no_routes
        self.false_alarm_rate = 0.025
        self.flag_attacker_type = 'uniform'
        self.rout_hops = []  # Stores all routes number of hops
        self.devices = []  # Stores all devices IDs
        self.devices_eff = []  # Stores all devices effectiveness values
        self.costs_importance_vector = []

        # Generate the devices IDs
        self.devices = []
        for dev in range(0, self.no_devices):
            self.devices.append(dev)
   
        # Routes in a dictionary, KEY is the route, VALUE is a list of the devices traverse the route
        self.routes = {}
        tmp_devices = deepcopy(self.devices)

        # Create the dictionary of routes
        for route in range(self.no_routes):
            current_dev_list = []
            random.shuffle(tmp_devices)

            # How many devices the current route will have
            no_devices_per_route = random.randint(self.no_min_devices_per_route, self.no_max_devices_per_route)

            # Create the list of devices for the current route by getting from the
            # shuffled list tmp_devices the first no_devices_per_route devices
            for dev in range(no_devices_per_route):
                current_dev_list.append(tmp_devices[dev])

            # Add the list of devices to the dictionary along with the key of the current route
            self.routes[route] = current_dev_list

        # Calculate all devices effectiveness values
        # Note: when giving the eff values for the last message consider that it is benign
        for dev in range(self.no_devices):
            self.dev_eff = []
            for msg in range(self.no_msgs):
                if msg != self.no_msgs - 1:
                    value = random.uniform(0.01, 0.99)
                else:
                    value = 1 - self.false_alarm_rate * self.no_mal_msgs
                self.dev_eff.append(value)
            self.devices_eff.append(self.dev_eff)
        
        self.average_device_eff_list = []
        self.dev_confusion_matrices = []  # Devices confusion matrices
        self.rout_confusion_matrices = []  # Routes confusion matrices
        self.sec_damage = 5    # damage = Hm
        self.false_alarm = 1  # false alarm = Hf

        # Energy costs units and lists
        self.sec_eng_cost_unit = 0.5  # a
        self.fwd_eng_cost_unit = 0.5  # b
        self.dev_sec_eng_costs = []
        self.dev_fwd_eng_costs = []
        self.dev_total_eng_costs = []
        self.rout_eng_costs = []

        # QoS
        self.max_hops = self.no_max_devices_per_route + 1
        self.rout_qos_cost = []

        # [route_Hm, route_Hf, route_energy_costs, route_hops]
        self.costs_importance_vector.append([10, 0.5, 0, 0])  # Security
        self.costs_importance_vector.append([5, 0.5, 5, 0])   # Security and Energy Efficiency
        self.costs_importance_vector.append([5, 0.5, 0, 5])   # Security and QoS
        self.costs_importance_vector.append([4, 0.5, 3, 2.5])   # Security, Energy Efficiency and QoS

        # Payoff matrices
        self.def_matrix = [[0] * self.no_msgs for i in range(self.no_routes)]
        self.att_matrix = [[0] * self.no_msgs for i in range(self.no_routes)]
        self.def_np_matrix = []
        self.att_np_matrix = []
        self.nash_smd_plan = []
        self.nash_attack_distr = []
        self.uniform_attack_distr = []
        self.aodv_plan = []
        self.aodv_route_id = -1
        self.all_simulations_avg_def_cost_smd = []
        self.all_simulations_avg_def_cost_aodv = []

    def compute_dev_conf_matrices(self):
        """
        Computes a list which contains all the devices confusion matrices.
        """

        cm_dev_row = []
        cm_dev = []
        # Compute the device confusion matrix for each device
        for device in range(0, self.no_devices):
            # All messages actually sent by the attacker
            for msg in range(0, self.no_msgs):
                # All messages for inspection
                for msg2 in range(0, self.no_msgs):
                    # message sent == message reported
                    if msg == msg2:
                        value = self.devices_eff[device][msg2]
                        cm_dev_row.append(value)
                    # Check whether we are iterating the innocent message sent by the
                    # attacker to set the false alarm
                    elif msg == self.no_msgs - 1:
                        if msg2 != self.no_msgs - 1:
                            cm_dev_row.append(self.false_alarm_rate)
                        else:
                            value = self.devices_eff[device][msg2]
                            cm_dev_row.append(value)
                    else:
                        if msg2 == self.no_msgs - 1:
                            cm_dev_row.append(1 - value)
                        else:
                            cm_dev_row.append(0)
                cm_dev.append(cm_dev_row)
                cm_dev_row = []
            self.dev_confusion_matrices.append(cm_dev)
            cm_dev = []

    def compute_route_conf_matrices_max(self):
        """
        Calculates all route confusion matrices.
        """

        # Iterate all routes
        for route in self.routes.keys():
            cm_rout = []
            for msg in range(self.no_msgs):  # Iterate messages actually sent by the attacker
                cm_rout_row = []
                sum_tmp = 0   # helpful variable to keep the sum of the false alarm rates
                for msg2 in range(self.no_msgs):   # Iterate messages of the defender's inspection
                    value = 0
                    # If the examined message is malicious - only the last msg (msg = self.no_msgs-1) is benign
                    if msg != self.no_msgs - 1:
                        for device in range(len(self.routes[route])):  # Iterate devices of each route
                            curr_device = self.routes[route][device]  # current device
                            if msg == msg2:  # message sent == message reported
                                if self.dev_confusion_matrices[curr_device][msg][msg2] > value:
                                    value = self.dev_confusion_matrices[curr_device][msg][msg2]
                                    max_detection = value
                            elif msg2 == self.no_msgs - 1:  # Message inspected as innocent
                                value = 1 - max_detection
                                break
                            else:
                                value = 0
                                break
                        cm_rout_row.append(value)
                    else:  # If the examined message is innocent
                        if msg2 != self.no_msgs - 1:   # message was not found innocent
                            # the false alarm rate on the route for this message
                            value = self.false_alarm_rate * len(self.routes[route])
                            cm_rout_row.append(value)
                            sum_tmp += value
                        else:
                            cm_rout_row.append(1 - sum_tmp)
                cm_rout.append(cm_rout_row)
            self.rout_confusion_matrices.append(cm_rout)

    def compute_route_conf_matrices_weighted(self):
        """
        Calculates all route confusion matrices.
        """

        # Iterate all routes
        for route in self.routes.keys():
            cm_rout = []
            for msg in range(self.no_msgs):  # Iterate messages actually sent by the attacker
                cm_rout_row = []
                sum_tmp = 0   # helpful variable to keep the sum of the false alarm rates
                total = 0
                for msg2 in range(self.no_msgs):   # Iterate messages of the defender's inspection
                    value = 0  # NO NEED FOR THAT
                    # If the examined message is malicious - only the last msg (msg = self.no_msgs-1) is benign
                    if msg != self.no_msgs - 1:
                        for device in range(len(self.routes[route])):  # Iterate devices of each route
                            curr_device = self.routes[route][device]  # current device
                            if msg == msg2:  # message sent == message reported
                                total += self.dev_confusion_matrices[curr_device][msg][msg2] / \
                                         self.no_max_devices_per_route
                                value = total
                            elif msg2 == self.no_msgs - 1:  # Message inspected as innocent
                                value = 1 - total
                                break
                            else:
                                value = 0
                                break
                        cm_rout_row.append(value)
                    else:  # If the examined message is innocent
                        if msg2 != self.no_msgs - 1:   # message was not found innocent
                            # the false alarm rate on the route for this message
                            value = self.false_alarm_rate * len(self.routes[route])
                            cm_rout_row.append(value)
                            sum_tmp += value
                        else:
                            cm_rout_row.append(1 - sum_tmp)
                cm_rout.append(cm_rout_row)
            self.rout_confusion_matrices.append(cm_rout)

    def compute_dev_eng_costs(self):
        """
        Derives the average devices costs.
        """

        # Devices average security effectiveness
        for device in range(self.no_devices):
            sum = 0
            for msg in range(self.no_msgs):
                sum += self.devices_eff[device][msg]
            average = sum / self.no_msgs
            self.average_device_eff_list.append(average)

        for device in range(self.no_devices):
            self.dev_sec_eng_costs.append(self.average_device_eff_list[device] * self.sec_eng_cost_unit)

        for device in range(self.no_devices):
            self.dev_fwd_eng_costs.append(self.fwd_eng_cost_unit)

        for device in range(self.no_devices):
            self.dev_total_eng_costs.append(self.dev_sec_eng_costs[device] + self.dev_fwd_eng_costs[device])

    def compute_rout_costs(self):
        """
        Derives the energy costs incurred in all routes.
        """

        for route in range(self.no_routes):
            rout_cost = 0
            for device in range(len(self.routes[route])):  # Iterate devices of each route
                curr_device = self.routes[route][device]  # current device
                rout_cost += self.dev_total_eng_costs[curr_device]
            self.rout_eng_costs.append(rout_cost)
        self.max_energy_cost = max(self.rout_eng_costs)

    def compute_hops(self):
        """
        Computes the hops of each route.
        """

        for route in self.routes.keys():
            self.rout_hops.append(len(self.routes[route]) + 1)

    def compute_route_qos(self):
        """
        Computes the QoS cost in terms of hops in the route and normalizes to be within [0,1].
        """

        for route in self.routes.keys():
            self.rout_qos_cost.append(float(self.rout_hops[route]) / float(self.max_hops))

    def solve_smd_game(self, importance):
        """
        Solves the bimatrix secure delivery message game.
        """

        self.nash_smd_plan = []
        self.nash_attack_distr = []
        self.aodv_plan = []

        if importance == 'Security Risk':
            costs_importance = self.costs_importance_vector[0]
        elif importance == 'Security Risk and Energy Consumption':
            costs_importance = self.costs_importance_vector[1]
        elif importance == 'Security Risk and QoS':
            costs_importance = self.costs_importance_vector[2]
        elif importance == 'Security Risk, Energy Consumption and QoS':
            costs_importance = self.costs_importance_vector[3]
        else:
            pass

        for route in range(self.no_routes):
            for msg in range(self.no_msgs):
                confusion = (1 - self.rout_confusion_matrices[route][msg][msg])
                if msg != self.no_msgs - 1:
                    damage_value = confusion * self.sec_damage * costs_importance[0]
                else:
                    damage_value = 0
                false_alarm_cost_value = confusion * self.false_alarm * costs_importance[1]
                energy_costs_value = self.rout_eng_costs[route] / self.max_energy_cost * costs_importance[2]
                qos_costs_value = self.rout_qos_cost[route] * costs_importance[3]
                self.def_matrix[route][msg] = - damage_value - false_alarm_cost_value \
                                              - energy_costs_value - qos_costs_value

        self.att_matrix = deepcopy(self.def_matrix)
        for route in range(len(self.att_matrix)):
            for msg in range(len(self.att_matrix[0])):
                    self.att_matrix[route][msg] = - self.att_matrix[route][msg]
        self.def_np_matrix = np.matrix(self.def_matrix)
        self.att_np_matrix = np.matrix(self.att_matrix)
 		
 		# Separate code must be used to solve the game
        game_sols = GS.all_ne(self.def_np_matrix, self.att_np_matrix, self.no_routes, self.no_msgs)

        defender = 0
        attacker = 1
        solution_id = 0
        bare_value = 0

        # Set the Nash defence distribution akin to Nash Message Delivery Plan
        for route in range(self.no_routes):
            print 'debugging:', game_sols[defender][solution_id][route][bare_value]
            self.nash_smd_plan.append(game_sols[defender][solution_id][route][bare_value])

        # Create the Nash attack distribution
        for msg in range(self.no_msgs):
            self.nash_attack_distr.append(game_sols[attacker][solution_id][msg][bare_value])

        # Create AODV routing plan
        for route in range(self.no_routes):
            if route != self.aodv_route_id:
                self.aodv_plan.append(0)
            else:
                self.aodv_plan.append(1)

    def compute_aodv_route(self):
        """
        Derives the AODV route.
        """
        for route in range(self.no_routes):
            self.aodv_route_id = self.rout_hops.index(min(self.rout_hops))

    def simulate(self):
        """
        Simulates the SMD game.
        """

        def_total_cost_smd = 0
        def_total_cost_aodv = 0
        sample_size = 1000

        for msg in range(self.no_msgs):
            self.uniform_attack_distr.append(1 / self.no_msgs)

        for sample in range(sample_size):
            # Randomize Defence
            def_pure_str = randomise_selection(self.nash_smd_plan)
            if self.flag_attacker_type == 'nash':
                att_pure_str = randomise_selection(self.nash_attack_distr)
            elif self.flag_attacker_type == 'uniform':
                att_pure_str = randomise_selection(self.uniform_attack_distr)
            # Calculate the Defender's Cost for this pair of pure strategies.
            def_total_cost_smd += self.def_matrix[def_pure_str][att_pure_str]
            def_total_cost_aodv += self.def_matrix[self.aodv_route_id][att_pure_str]

        print '\nCost of the defender in SMD:', def_total_cost_smd
        print '\nCost of the defender in AODV:', def_total_cost_aodv

        return def_total_cost_smd, def_total_cost_aodv


def scenarios(no_mal_msgs_set):
    scenarios_results = []
    all_importance = ['Security Risk','Security Risk and Energy Consumption',
                      'Security Risk and QoS', 'Security Risk, Energy Consumption and QoS']
    flag = 'no_mal_messages'

    # Vary the number of malicious messages
    if flag == 'no_mal_messages':
        # Take results for different number of malicious messages
        for i in range(len(no_mal_msgs_set)):
            scenario_results = []
            print '\n===Number of Malicious Messages:', no_mal_msgs_set[i]
            # For current number of messages and 6 routes
            smd = SMD(no_mal_msgs_set[i], 6)
            # Compute the confusion matrices of the devices
            smd.compute_dev_conf_matrices()
            # Compute the confusion matrices of the routes
            smd.compute_route_conf_matrices_weighted()
            # Compute the energy costs of the devices
            smd.compute_dev_eng_costs()
            # Compute the hops of each route
            smd.compute_hops()
            # Compute the QoS cost in terms of hops in the route and normalizes to be within [0,1]
            smd.compute_route_qos()
            # Derive the energy costs incurred in all routes
            smd.compute_rout_costs()
            # Derive the AODV route
            smd.compute_aodv_route()
            # Traverse the different profiles to retrieve results
            for importance in range(len(all_importance)):
                # Solve the bimatrix secure delivery message game
                smd.solve_smd_game(all_importance[importance])
                # Simulate the SMD game
                importance_results = smd.simulate()
                # Save the results of the different scenarios when importance varies
                scenario_results.append(importance_results)
            # Save the results of the different scenarios when no_malicious messages varies
            scenarios_results.append(scenario_results)
    return scenarios_results


def randomise_selection(distribution):
    """
    Returns a position in the probability distribution, that
    indicates the pure strategy a player chooses.
    """

    selection = random.random()
    strategy = 0
    count = 0
    for i in range(len(distribution)):
        count += distribution[i]
        if selection < count:
            strategy = i
            break
    return strategy


def take_results():
    diffs_per_no_msgs = []
    no_mal_msgs_set = []
    #no_routes_set = []
    for i in range(1, diff_no_mal_msgs):
        # This set keeps all the number of different malicious messages
        no_mal_msgs_set.append(i * step)

    # Call the method that consists of all the steps of the SMD protocol
    all_results = scenarios(no_mal_msgs_set)

    # Derive the difference of improvement of SMD over AODV
    for no_msgs_idx in range(len(all_results)):
        diffs_per_profile = []
        for importance in range(len(all_results[0])):
            diffs_per_profile.append((all_results[no_msgs_idx][importance][0]
                                     - all_results[no_msgs_idx][importance][1])
                                     / (-all_results[no_msgs_idx][importance][1]) * 100)
        diffs_per_no_msgs.append(diffs_per_profile)

    return diffs_per_no_msgs


def plot_profile_1(ax, avg_imp_prof_1, std_dev_prof_1):
    x = np.arange(step, step * diff_no_mal_msgs, step)
    ax.grid(True)
    ax.set_xlabel('number of available malicious messages', fontsize=12)
    ax.set_ylabel('defender\'s cost improvement in %', fontsize=12)
    ax.set_title('SMD - Security Profile', fontsize=12)
    ax.errorbar(x, avg_imp_prof_1, color='#696969', label="Security",
                linewidth=2, yerr=std_dev_prof_1, fmt='-o', linestyle="dashed")
    ax.xaxis.set_ticks(np.arange(step, step * diff_no_mal_msgs + step, step))


def plot_profile_2(ax, avg_imp_prof_2, std_dev_prof_2):
    x = np.arange(step, step * diff_no_mal_msgs, step)
    ax.grid(True)
    ax.set_xlabel('number of available malicious messages', fontsize=12)
    ax.set_ylabel('defender\'s cost improvement in %', fontsize=12)
    ax.set_title('SMD - Security & Energy Efficiency Profile', fontsize=12)
    ax.errorbar(x, avg_imp_prof_2, color='#696969', label="Security & Energy Efficiency",
                linewidth=2, yerr=std_dev_prof_2, fmt='-o', linestyle="dashed")
    ax.xaxis.set_ticks(np.arange(step, step * diff_no_mal_msgs + step, step))


def plot_profile_3(ax, avg_imp_prof_3, std_dev_prof_3):
    x = np.arange(step, step * diff_no_mal_msgs, step)
    ax.grid(True)
    ax.set_xlabel('number of available malicious messages', fontsize=12)
    ax.set_ylabel('defender\'s cost improvement in %', fontsize=12)
    ax.set_title('SMD - Security & QoS Profile', fontsize=12)
    ax.errorbar(x, avg_imp_prof_3, color='#696969', label="Security & QoS",
                linewidth=2, yerr=std_dev_prof_3, fmt='-o', linestyle="dashed")
    ax.xaxis.set_ticks(np.arange(step, step * diff_no_mal_msgs + step, step))


def plot_profile_4(ax, avg_imp_prof_4, std_dev_prof_4):
    x = np.arange(step, step * diff_no_mal_msgs, step)
    ax.grid(True)
    ax.set_xlabel('number of available malicious messages', fontsize=12)
    ax.set_ylabel('defender\'s cost improvement in %', fontsize=12)
    ax.set_title('SMD - Security & QoS & Energy Efficiency Profile', fontsize=12)
    ax.errorbar(x, avg_imp_prof_4, color='#696969', label="All-3-in-1",
                linewidth=2, yerr=std_dev_prof_4, fmt='-o', linestyle="dashed")
    ax.xaxis.set_ticks(np.arange(step, step * diff_no_mal_msgs + step, step))


if __name__ == '__main__':
    runs = 25
    final_results = []
    avg_diffs_per_no_msgs_all_profiles = []
    final_avg_results = []

    final_results_avg_list = []
    final_results_std_deviation_list = []
    final_results_avg_list_per_bar = []
    final_results_std_deviation_list_per_bar = []

    for run in range(runs):
        print '================'
        print 'Run:', run
        print '================'
        diffs_per_no_msgs_per_run = take_results()
        final_results.append(diffs_per_no_msgs_per_run)

    print '\nFinal_results:'
    for i in range(len(final_results)):
        for j in range(len(final_results[0])):
            print final_results[i][j]
        print ''

    avg_imp_list = []
    std_dev_list = []
    avg_imp = 0

    # Derive the final average values
    for profile in range(len(final_results[0][0])):
        imp_avg_profile = []
        std_dev_profile = []
        #avg_diffs_per_no_msgs_all_profiles = []
        #temp_list = []
        for no_msgs_idx in range(len(final_results[0])):
            imp_per_run = []
            sum = 0
            for run in range(len(final_results)):
                imp_per_run.append(final_results[run][no_msgs_idx][profile])
                sum += imp_per_run[run]
            avg_imp = sum / runs
            imp_var = map(lambda temp: (temp - avg_imp) ** 2, imp_per_run)
            sum = 0
            for i in range(len(imp_var)):
                sum += imp_var[i]
            avg_var = sum / len(imp_var)
            std_dev = math.sqrt(avg_var)
            # Store the avg improvement for the pair <profile,no_msgs>
            imp_avg_profile.append(avg_imp)
            # Store the std dev for the pair <profile,no_msgs>
            std_dev_profile.append(std_dev)
        avg_imp_list.append(imp_avg_profile)
        std_dev_list.append(std_dev_profile)

    print '\nimp_avg_list:'
    for i in range(len(avg_imp_list)):
        print avg_imp_list[i]

    print '\nstd_dev_list:'
    for i in range(len(std_dev_list)):
        print std_dev_list[i]

    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(nrows=2, ncols=2)

    avg_imp_prof_1 = avg_imp_list[0]
    std_dev_prof_1 = std_dev_list[0]
    avg_imp_prof_2 = avg_imp_list[1]
    std_dev_prof_2 = std_dev_list[1]
    avg_imp_prof_3 = avg_imp_list[2]
    std_dev_prof_3 = std_dev_list[2]
    avg_imp_prof_4 = avg_imp_list[3]
    std_dev_prof_4 = std_dev_list[3]

    plot_profile_1(ax1, avg_imp_prof_1, std_dev_prof_1)
    plot_profile_2(ax2, avg_imp_prof_2, std_dev_prof_2)
    plot_profile_3(ax3, avg_imp_prof_3, std_dev_prof_3)
    plot_profile_4(ax4, avg_imp_prof_4, std_dev_prof_4)
    plt.tight_layout()
    plt.show()

