-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp058
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T00:53:05.258627+00:00
-- url     : https://prove2.me/submissions/beb6074d-b39f-4b01-aacc-78e147553f28

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02851
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02852
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02853
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02854
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02855
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02856
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02857
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02858
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02859
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02860
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02861
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02862
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02863
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02864
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02865
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02866
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02867
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02868
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02869
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02870
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02871
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02872
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02873
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02874
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02875
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02876
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02877
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02878
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02879
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02880
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02881
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02882
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02883
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02884
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02885
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02886
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02887
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02888
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02889
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02890
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02891
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02892
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02893
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02894
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02895
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02896
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02897
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02898
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02899
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02900

theorem solution (n : Nat)
    (hn : 10473534734783 < n) (hupper : n <= 11851275819517) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 11141128710617 n with h2 | h2
  · -- n > 11141128710617
    rcases Nat.lt_or_ge 11476525615787 n with h4 | h4
    · -- n > 11476525615787
      rcases Nat.lt_or_ge 11647991626993 n with h6 | h6
      · -- n > 11647991626993
        rcases Nat.lt_or_ge 11734682929687 n with h8 | h8
        · -- n > 11734682929687
          rcases Nat.lt_or_ge 11792835284851 n with h10 | h10
          · -- n > 11792835284851
            rcases Nat.lt_or_ge 11822019440731 n with h12 | h12
            · -- n > 11822019440731
              exact RamareSaouter2003.prime_interval_nat_ladder_c02900 n (by omega) (by omega)
            · -- n <= 11822019440731
              exact RamareSaouter2003.prime_interval_nat_ladder_c02899 n (by omega) (by omega)
          · -- n <= 11792835284851
            rcases Nat.lt_or_ge 11763723173737 n with h12 | h12
            · -- n > 11763723173737
              exact RamareSaouter2003.prime_interval_nat_ladder_c02898 n (by omega) (by omega)
            · -- n <= 11763723173737
              exact RamareSaouter2003.prime_interval_nat_ladder_c02897 n (by omega) (by omega)
        · -- n <= 11734682929687
          rcases Nat.lt_or_ge 11676817333073 n with h10 | h10
          · -- n > 11676817333073
            rcases Nat.lt_or_ge 11705714375071 n with h12 | h12
            · -- n > 11705714375071
              exact RamareSaouter2003.prime_interval_nat_ladder_c02896 n (by omega) (by omega)
            · -- n <= 11705714375071
              exact RamareSaouter2003.prime_interval_nat_ladder_c02895 n (by omega) (by omega)
          · -- n <= 11676817333073
            exact RamareSaouter2003.prime_interval_nat_ladder_c02894 n (by omega) (by omega)
      · -- n <= 11647991626993
        rcases Nat.lt_or_ge 11561940766081 n with h8 | h8
        · -- n > 11561940766081
          rcases Nat.lt_or_ge 11590553518969 n with h10 | h10
          · -- n > 11590553518969
            rcases Nat.lt_or_ge 11619237080833 n with h12 | h12
            · -- n > 11619237080833
              exact RamareSaouter2003.prime_interval_nat_ladder_c02893 n (by omega) (by omega)
            · -- n <= 11619237080833
              exact RamareSaouter2003.prime_interval_nat_ladder_c02892 n (by omega) (by omega)
          · -- n <= 11590553518969
            exact RamareSaouter2003.prime_interval_nat_ladder_c02891 n (by omega) (by omega)
        · -- n <= 11561940766081
          rcases Nat.lt_or_ge 11504926988689 n with h10 | h10
          · -- n > 11504926988689
            rcases Nat.lt_or_ge 11533398647539 n with h12 | h12
            · -- n > 11533398647539
              exact RamareSaouter2003.prime_interval_nat_ladder_c02890 n (by omega) (by omega)
            · -- n <= 11533398647539
              exact RamareSaouter2003.prime_interval_nat_ladder_c02889 n (by omega) (by omega)
          · -- n <= 11504926988689
            exact RamareSaouter2003.prime_interval_nat_ladder_c02888 n (by omega) (by omega)
    · -- n <= 11476525615787
      rcases Nat.lt_or_ge 11307583695719 n with h6 | h6
      · -- n > 11307583695719
        rcases Nat.lt_or_ge 11391741479617 n with h8 | h8
        · -- n > 11391741479617
          rcases Nat.lt_or_ge 11419933034161 n with h10 | h10
          · -- n > 11419933034161
            rcases Nat.lt_or_ge 11448194355401 n with h12 | h12
            · -- n > 11448194355401
              exact RamareSaouter2003.prime_interval_nat_ladder_c02887 n (by omega) (by omega)
            · -- n <= 11448194355401
              exact RamareSaouter2003.prime_interval_nat_ladder_c02886 n (by omega) (by omega)
          · -- n <= 11419933034161
            exact RamareSaouter2003.prime_interval_nat_ladder_c02885 n (by omega) (by omega)
        · -- n <= 11391741479617
          rcases Nat.lt_or_ge 11335566981979 n with h10 | h10
          · -- n > 11335566981979
            rcases Nat.lt_or_ge 11363619519467 n with h12 | h12
            · -- n > 11363619519467
              exact RamareSaouter2003.prime_interval_nat_ladder_c02884 n (by omega) (by omega)
            · -- n <= 11363619519467
              exact RamareSaouter2003.prime_interval_nat_ladder_c02883 n (by omega) (by omega)
          · -- n <= 11335566981979
            exact RamareSaouter2003.prime_interval_nat_ladder_c02882 n (by omega) (by omega)
      · -- n <= 11307583695719
        rcases Nat.lt_or_ge 11224047637139 n with h8 | h8
        · -- n > 11224047637139
          rcases Nat.lt_or_ge 11251824193697 n with h10 | h10
          · -- n > 11251824193697
            rcases Nat.lt_or_ge 11279669489909 n with h12 | h12
            · -- n > 11279669489909
              exact RamareSaouter2003.prime_interval_nat_ladder_c02881 n (by omega) (by omega)
            · -- n <= 11279669489909
              exact RamareSaouter2003.prime_interval_nat_ladder_c02880 n (by omega) (by omega)
          · -- n <= 11251824193697
            exact RamareSaouter2003.prime_interval_nat_ladder_c02879 n (by omega) (by omega)
        · -- n <= 11224047637139
          rcases Nat.lt_or_ge 11168700064649 n with h10 | h10
          · -- n > 11168700064649
            rcases Nat.lt_or_ge 11196339650549 n with h12 | h12
            · -- n > 11196339650549
              exact RamareSaouter2003.prime_interval_nat_ladder_c02878 n (by omega) (by omega)
            · -- n <= 11196339650549
              exact RamareSaouter2003.prime_interval_nat_ladder_c02877 n (by omega) (by omega)
          · -- n <= 11168700064649
            exact RamareSaouter2003.prime_interval_nat_ladder_c02876 n (by omega) (by omega)
  · -- n <= 11141128710617
    rcases Nat.lt_or_ge 10788834128983 n with h4 | h4
    · -- n > 10788834128983
      rcases Nat.lt_or_ge 10950025627031 n with h6 | h6
      · -- n > 10950025627031
        rcases Nat.lt_or_ge 11031522250283 n with h8 | h8
        · -- n > 11031522250283
          rcases Nat.lt_or_ge 11086190024717 n with h10 | h10
          · -- n > 11086190024717
            rcases Nat.lt_or_ge 11113625419961 n with h12 | h12
            · -- n > 11113625419961
              exact RamareSaouter2003.prime_interval_nat_ladder_c02875 n (by omega) (by omega)
            · -- n <= 11113625419961
              exact RamareSaouter2003.prime_interval_nat_ladder_c02874 n (by omega) (by omega)
          · -- n <= 11086190024717
            rcases Nat.lt_or_ge 11058822357293 n with h12 | h12
            · -- n > 11058822357293
              exact RamareSaouter2003.prime_interval_nat_ladder_c02873 n (by omega) (by omega)
            · -- n <= 11058822357293
              exact RamareSaouter2003.prime_interval_nat_ladder_c02872 n (by omega) (by omega)
        · -- n <= 11031522250283
          rcases Nat.lt_or_ge 10977124051241 n with h10 | h10
          · -- n > 10977124051241
            rcases Nat.lt_or_ge 11004289537037 n with h12 | h12
            · -- n > 11004289537037
              exact RamareSaouter2003.prime_interval_nat_ladder_c02871 n (by omega) (by omega)
            · -- n <= 11004289537037
              exact RamareSaouter2003.prime_interval_nat_ladder_c02870 n (by omega) (by omega)
          · -- n <= 10977124051241
            exact RamareSaouter2003.prime_interval_nat_ladder_c02869 n (by omega) (by omega)
      · -- n <= 10950025627031
        rcases Nat.lt_or_ge 10869131069143 n with h8 | h8
        · -- n > 10869131069143
          rcases Nat.lt_or_ge 10896029300839 n with h10 | h10
          · -- n > 10896029300839
            rcases Nat.lt_or_ge 10922994098561 n with h12 | h12
            · -- n > 10922994098561
              exact RamareSaouter2003.prime_interval_nat_ladder_c02868 n (by omega) (by omega)
            · -- n <= 10922994098561
              exact RamareSaouter2003.prime_interval_nat_ladder_c02867 n (by omega) (by omega)
          · -- n <= 10896029300839
            exact RamareSaouter2003.prime_interval_nat_ladder_c02866 n (by omega) (by omega)
        · -- n <= 10869131069143
          rcases Nat.lt_or_ge 10815533646941 n with h10 | h10
          · -- n > 10815533646941
            rcases Nat.lt_or_ge 10842299239159 n with h12 | h12
            · -- n > 10842299239159
              exact RamareSaouter2003.prime_interval_nat_ladder_c02865 n (by omega) (by omega)
            · -- n <= 10842299239159
              exact RamareSaouter2003.prime_interval_nat_ladder_c02864 n (by omega) (by omega)
          · -- n <= 10815533646941
            exact RamareSaouter2003.prime_interval_nat_ladder_c02863 n (by omega) (by omega)
    · -- n <= 10788834128983
      rcases Nat.lt_or_ge 10630015474777 n with h6 | h6
      · -- n > 10630015474777
        rcases Nat.lt_or_ge 10709130391621 n with h8 | h8
        · -- n > 10709130391621
          rcases Nat.lt_or_ge 10735632663827 n with h10 | h10
          · -- n > 10735632663827
            rcases Nat.lt_or_ge 10762200522181 n with h12 | h12
            · -- n > 10762200522181
              exact RamareSaouter2003.prime_interval_nat_ladder_c02862 n (by omega) (by omega)
            · -- n <= 10762200522181
              exact RamareSaouter2003.prime_interval_nat_ladder_c02861 n (by omega) (by omega)
          · -- n <= 10735632663827
            exact RamareSaouter2003.prime_interval_nat_ladder_c02860 n (by omega) (by omega)
        · -- n <= 10709130391621
          rcases Nat.lt_or_ge 10656321958463 n with h10 | h10
          · -- n > 10656321958463
            rcases Nat.lt_or_ge 10682693543677 n with h12 | h12
            · -- n > 10682693543677
              exact RamareSaouter2003.prime_interval_nat_ladder_c02859 n (by omega) (by omega)
            · -- n <= 10682693543677
              exact RamareSaouter2003.prime_interval_nat_ladder_c02858 n (by omega) (by omega)
          · -- n <= 10656321958463
            exact RamareSaouter2003.prime_interval_nat_ladder_c02857 n (by omega) (by omega)
      · -- n <= 10630015474777
        rcases Nat.lt_or_ge 10551485028311 n with h8 | h8
        · -- n > 10551485028311
          rcases Nat.lt_or_ge 10577597169803 n with h10 | h10
          · -- n > 10577597169803
            rcases Nat.lt_or_ge 10603773931997 n with h12 | h12
            · -- n > 10603773931997
              exact RamareSaouter2003.prime_interval_nat_ladder_c02856 n (by omega) (by omega)
            · -- n <= 10603773931997
              exact RamareSaouter2003.prime_interval_nat_ladder_c02855 n (by omega) (by omega)
          · -- n <= 10577597169803
            exact RamareSaouter2003.prime_interval_nat_ladder_c02854 n (by omega) (by omega)
        · -- n <= 10551485028311
          rcases Nat.lt_or_ge 10499453969813 n with h10 | h10
          · -- n > 10499453969813
            rcases Nat.lt_or_ge 10525437347959 n with h12 | h12
            · -- n > 10525437347959
              exact RamareSaouter2003.prime_interval_nat_ladder_c02853 n (by omega) (by omega)
            · -- n <= 10525437347959
              exact RamareSaouter2003.prime_interval_nat_ladder_c02852 n (by omega) (by omega)
          · -- n <= 10499453969813
            exact RamareSaouter2003.prime_interval_nat_ladder_c02851 n (by omega) (by omega)
