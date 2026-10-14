-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp160
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T11:02:54.84477+00:00
-- url     : https://prove2.me/submissions/184882f0-bbb6-4c91-99b9-92c1f58acb7e

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07934
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07935
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07936
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07937
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07938
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07939
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07940
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07941
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07942
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07943
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07944
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07945
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07946
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07947
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07948
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07949
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07950
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07951
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07952
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07953
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07954
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07955
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07956
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07957
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07958
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07959
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07960
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07961
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07962
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07963
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07964
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07965
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07966
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07967
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07968
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07969
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07970
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07971
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07972
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07973
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07974
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07975
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07976
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07977
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07978
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07979
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07980
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07981
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07982

theorem solution (n : Nat)
    (hn : 12423819217158574193 < n) (hupper : n <= 14269908471619535531) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 13296097716121785079 n with h2 | h2
  · -- n > 13296097716121785079
    rcases Nat.lt_or_ge 13754941024823835169 n with h4 | h4
    · -- n > 13754941024823835169
      rcases Nat.lt_or_ge 13990267558134265439 n with h6 | h6
      · -- n > 13990267558134265439
        rcases Nat.lt_or_ge 14109436317755035963 n with h8 | h8
        · -- n > 14109436317755035963
          rcases Nat.lt_or_ge 14189445604596342173 n with h10 | h10
          · -- n > 14189445604596342173
            rcases Nat.lt_or_ge 14229620200543806427 n with h12 | h12
            · -- n > 14229620200543806427
              exact RamareSaouter2003.prime_interval_nat_ladder_c07982 n (by omega) (by omega)
            · -- n <= 14229620200543806427
              exact RamareSaouter2003.prime_interval_nat_ladder_c07981 n (by omega) (by omega)
          · -- n <= 14189445604596342173
            rcases Nat.lt_or_ge 14149384389793037663 n with h12 | h12
            · -- n > 14149384389793037663
              exact RamareSaouter2003.prime_interval_nat_ladder_c07980 n (by omega) (by omega)
            · -- n <= 14149384389793037663
              exact RamareSaouter2003.prime_interval_nat_ladder_c07979 n (by omega) (by omega)
        · -- n <= 14109436317755035963
          rcases Nat.lt_or_ge 14029878106307549687 n with h10 | h10
          · -- n > 14029878106307549687
            rcases Nat.lt_or_ge 14069600989215101357 n with h12 | h12
            · -- n > 14069600989215101357
              exact RamareSaouter2003.prime_interval_nat_ladder_c07978 n (by omega) (by omega)
            · -- n <= 14069600989215101357
              exact RamareSaouter2003.prime_interval_nat_ladder_c07977 n (by omega) (by omega)
          · -- n <= 14029878106307549687
            exact RamareSaouter2003.prime_interval_nat_ladder_c07976 n (by omega) (by omega)
      · -- n <= 13990267558134265439
        rcases Nat.lt_or_ge 13872105279827823569 n with h8 | h8
        · -- n > 13872105279827823569
          rcases Nat.lt_or_ge 13911381429361040333 n with h10 | h10
          · -- n > 13911381429361040333
            rcases Nat.lt_or_ge 13950768664891947179 n with h12 | h12
            · -- n > 13950768664891947179
              exact RamareSaouter2003.prime_interval_nat_ladder_c07975 n (by omega) (by omega)
            · -- n <= 13950768664891947179
              exact RamareSaouter2003.prime_interval_nat_ladder_c07974 n (by omega) (by omega)
          · -- n <= 13911381429361040333
            exact RamareSaouter2003.prime_interval_nat_ladder_c07973 n (by omega) (by omega)
        · -- n <= 13872105279827823569
          rcases Nat.lt_or_ge 13793885341905259271 n with h10 | h10
          · -- n > 13793885341905259271
            rcases Nat.lt_or_ge 13832940047632204507 n with h12 | h12
            · -- n > 13832940047632204507
              exact RamareSaouter2003.prime_interval_nat_ladder_c07972 n (by omega) (by omega)
            · -- n <= 13832940047632204507
              exact RamareSaouter2003.prime_interval_nat_ladder_c07971 n (by omega) (by omega)
          · -- n <= 13793885341905259271
            exact RamareSaouter2003.prime_interval_nat_ladder_c07970 n (by omega) (by omega)
    · -- n <= 13754941024823835169
      rcases Nat.lt_or_ge 13523573045508834619 n with h6 | h6
      · -- n > 13523573045508834619
        rcases Nat.lt_or_ge 13638766462827484639 n with h8 | h8
        · -- n > 13638766462827484639
          rcases Nat.lt_or_ge 13677381976939482079 n with h10 | h10
          · -- n > 13677381976939482079
            rcases Nat.lt_or_ge 13716106521272552009 n with h12 | h12
            · -- n > 13716106521272552009
              exact RamareSaouter2003.prime_interval_nat_ladder_c07969 n (by omega) (by omega)
            · -- n <= 13716106521272552009
              exact RamareSaouter2003.prime_interval_nat_ladder_c07968 n (by omega) (by omega)
          · -- n <= 13677381976939482079
            exact RamareSaouter2003.prime_interval_nat_ladder_c07967 n (by omega) (by omega)
        · -- n <= 13638766462827484639
          rcases Nat.lt_or_ge 13561862364334453753 n with h10 | h10
          · -- n > 13561862364334453753
            rcases Nat.lt_or_ge 13600259970344090819 n with h12 | h12
            · -- n > 13600259970344090819
              exact RamareSaouter2003.prime_interval_nat_ladder_c07966 n (by omega) (by omega)
            · -- n <= 13600259970344090819
              exact RamareSaouter2003.prime_interval_nat_ladder_c07965 n (by omega) (by omega)
          · -- n <= 13561862364334453753
            exact RamareSaouter2003.prime_interval_nat_ladder_c07964 n (by omega) (by omega)
      · -- n <= 13523573045508834619
        rcases Nat.lt_or_ge 13409353073711382559 n with h8 | h8
        · -- n > 13409353073711382559
          rcases Nat.lt_or_ge 13447319073085848383 n with h10 | h10
          · -- n > 13447319073085848383
            rcases Nat.lt_or_ge 13485392336372726813 n with h12 | h12
            · -- n > 13485392336372726813
              exact RamareSaouter2003.prime_interval_nat_ladder_c07963 n (by omega) (by omega)
            · -- n <= 13485392336372726813
              exact RamareSaouter2003.prime_interval_nat_ladder_c07962 n (by omega) (by omega)
          · -- n <= 13447319073085848383
            exact RamareSaouter2003.prime_interval_nat_ladder_c07961 n (by omega) (by omega)
        · -- n <= 13409353073711382559
          rcases Nat.lt_or_ge 13333742753844783349 n with h10 | h10
          · -- n > 13333742753844783349
            rcases Nat.lt_or_ge 13371494314852619587 n with h12 | h12
            · -- n > 13371494314852619587
              exact RamareSaouter2003.prime_interval_nat_ladder_c07960 n (by omega) (by omega)
            · -- n <= 13371494314852619587
              exact RamareSaouter2003.prime_interval_nat_ladder_c07959 n (by omega) (by omega)
          · -- n <= 13333742753844783349
            exact RamareSaouter2003.prime_interval_nat_ladder_c07958 n (by omega) (by omega)
  · -- n <= 13296097716121785079
    rcases Nat.lt_or_ge 12852561050364074621 n with h4 | h4
    · -- n > 12852561050364074621
      rcases Nat.lt_or_ge 13072447653388755679 n with h6 | h6
      · -- n > 13072447653388755679
        rcases Nat.lt_or_ge 13183798643366000861 n with h8 | h8
        · -- n > 13183798643366000861
          rcases Nat.lt_or_ge 13221125976639663301 n with h10 | h10
          · -- n > 13221125976639663301
            rcases Nat.lt_or_ge 13258558671240955217 n with h12 | h12
            · -- n > 13258558671240955217
              exact RamareSaouter2003.prime_interval_nat_ladder_c07957 n (by omega) (by omega)
            · -- n <= 13258558671240955217
              exact RamareSaouter2003.prime_interval_nat_ladder_c07956 n (by omega) (by omega)
          · -- n <= 13221125976639663301
            exact RamareSaouter2003.prime_interval_nat_ladder_c07955 n (by omega) (by omega)
        · -- n <= 13183798643366000861
          rcases Nat.lt_or_ge 13109459759414939507 n with h10 | h10
          · -- n > 13109459759414939507
            rcases Nat.lt_or_ge 13146576645556833793 n with h12 | h12
            · -- n > 13146576645556833793
              exact RamareSaouter2003.prime_interval_nat_ladder_c07954 n (by omega) (by omega)
            · -- n <= 13146576645556833793
              exact RamareSaouter2003.prime_interval_nat_ladder_c07953 n (by omega) (by omega)
          · -- n <= 13109459759414939507
            exact RamareSaouter2003.prime_interval_nat_ladder_c07952 n (by omega) (by omega)
      · -- n <= 13072447653388755679
        rcases Nat.lt_or_ge 12962038017572819957 n with h8 | h8
        · -- n > 12962038017572819957
          rcases Nat.lt_or_ge 12998737523100101167 n with h10 | h10
          · -- n > 12998737523100101167
            rcases Nat.lt_or_ge 13035540561318041947 n with h12 | h12
            · -- n > 13035540561318041947
              exact RamareSaouter2003.prime_interval_nat_ladder_c07951 n (by omega) (by omega)
            · -- n <= 13035540561318041947
              exact RamareSaouter2003.prime_interval_nat_ladder_c07950 n (by omega) (by omega)
          · -- n <= 12998737523100101167
            exact RamareSaouter2003.prime_interval_nat_ladder_c07949 n (by omega) (by omega)
        · -- n <= 12962038017572819957
          rcases Nat.lt_or_ge 12888949846872418919 n with h10 | h10
          · -- n > 12888949846872418919
            rcases Nat.lt_or_ge 12925442162889206749 n with h12 | h12
            · -- n > 12925442162889206749
              exact RamareSaouter2003.prime_interval_nat_ladder_c07948 n (by omega) (by omega)
            · -- n <= 12925442162889206749
              exact RamareSaouter2003.prime_interval_nat_ladder_c07947 n (by omega) (by omega)
          · -- n <= 12888949846872418919
            exact RamareSaouter2003.prime_interval_nat_ladder_c07946 n (by omega) (by omega)
    · -- n <= 12852561050364074621
      rcases Nat.lt_or_ge 12636371592163219841 n with h6 | h6
      · -- n > 12636371592163219841
        rcases Nat.lt_or_ge 12744007941607988509 n with h8 | h8
        · -- n > 12744007941607988509
          rcases Nat.lt_or_ge 12780090135645087049 n with h10 | h10
          · -- n > 12780090135645087049
            rcases Nat.lt_or_ge 12816274424063981251 n with h12 | h12
            · -- n > 12816274424063981251
              exact RamareSaouter2003.prime_interval_nat_ladder_c07945 n (by omega) (by omega)
            · -- n <= 12816274424063981251
              exact RamareSaouter2003.prime_interval_nat_ladder_c07944 n (by omega) (by omega)
          · -- n <= 12780090135645087049
            exact RamareSaouter2003.prime_interval_nat_ladder_c07943 n (by omega) (by omega)
        · -- n <= 12744007941607988509
          rcases Nat.lt_or_ge 12672148992004158379 n with h10 | h10
          · -- n > 12672148992004158379
            rcases Nat.lt_or_ge 12708027668041088947 n with h12 | h12
            · -- n > 12708027668041088947
              exact RamareSaouter2003.prime_interval_nat_ladder_c07942 n (by omega) (by omega)
            · -- n <= 12708027668041088947
              exact RamareSaouter2003.prime_interval_nat_ladder_c07941 n (by omega) (by omega)
          · -- n <= 12672148992004158379
            exact RamareSaouter2003.prime_interval_nat_ladder_c07940 n (by omega) (by omega)
      · -- n <= 12636371592163219841
        rcases Nat.lt_or_ge 12529644732131093311 n with h8 | h8
        · -- n > 12529644732131093311
          rcases Nat.lt_or_ge 12565119995144813263 n with h10 | h10
          · -- n > 12565119995144813263
            rcases Nat.lt_or_ge 12600695267165025623 n with h12 | h12
            · -- n > 12600695267165025623
              exact RamareSaouter2003.prime_interval_nat_ladder_c07939 n (by omega) (by omega)
            · -- n <= 12600695267165025623
              exact RamareSaouter2003.prime_interval_nat_ladder_c07938 n (by omega) (by omega)
          · -- n <= 12565119995144813263
            exact RamareSaouter2003.prime_interval_nat_ladder_c07937 n (by omega) (by omega)
        · -- n <= 12529644732131093311
          rcases Nat.lt_or_ge 12458994774103364083 n with h10 | h10
          · -- n > 12458994774103364083
            rcases Nat.lt_or_ge 12494269882603861951 n with h12 | h12
            · -- n > 12494269882603861951
              exact RamareSaouter2003.prime_interval_nat_ladder_c07936 n (by omega) (by omega)
            · -- n <= 12494269882603861951
              exact RamareSaouter2003.prime_interval_nat_ladder_c07935 n (by omega) (by omega)
          · -- n <= 12458994774103364083
            exact RamareSaouter2003.prime_interval_nat_ladder_c07934 n (by omega) (by omega)
