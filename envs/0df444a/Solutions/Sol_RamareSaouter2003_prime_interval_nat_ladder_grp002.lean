-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp002
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T14:04:00.783403+00:00
-- url     : https://prove2.me/submissions/f6f27ac8-dc57-4113-87f0-27d6a68cb181

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00051
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00052
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00053
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00054
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00055
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00056
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00057
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00058
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00059
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00060
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00061
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00062
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00063
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00064
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00065
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00066
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00067
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00068
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00069
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00070
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00071
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00072
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00073
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00074
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00075
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00076
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00077
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00078
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00079
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00080
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00081
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00082
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00083
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00084
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00085
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00086
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00087
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00088
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00089
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00090
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00091
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00092
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00093
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00094
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00095
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00096
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00097
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00098
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00099
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00100

theorem solution (n : Nat)
    (hn : 11947020167 < n) (hupper : n <= 13313012261) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 12610692923 n with h2 | h2
  · -- n > 12610692923
    rcases Nat.lt_or_ge 12942841669 n with h4 | h4
    · -- n > 12942841669
      rcases Nat.lt_or_ge 13112334049 n with h6 | h6
      · -- n > 13112334049
        rcases Nat.lt_or_ge 13197948889 n with h8 | h8
        · -- n > 13197948889
          rcases Nat.lt_or_ge 13255350037 n with h10 | h10
          · -- n > 13255350037
            rcases Nat.lt_or_ge 13284148439 n with h12 | h12
            · -- n > 13284148439
              exact RamareSaouter2003.prime_interval_nat_ladder_c00100 n (by omega) (by omega)
            · -- n <= 13284148439
              exact RamareSaouter2003.prime_interval_nat_ladder_c00099 n (by omega) (by omega)
          · -- n <= 13255350037
            rcases Nat.lt_or_ge 13226616899 n with h12 | h12
            · -- n > 13226616899
              exact RamareSaouter2003.prime_interval_nat_ladder_c00098 n (by omega) (by omega)
            · -- n <= 13226616899
              exact RamareSaouter2003.prime_interval_nat_ladder_c00097 n (by omega) (by omega)
        · -- n <= 13197948889
          rcases Nat.lt_or_ge 13140807661 n with h10 | h10
          · -- n > 13140807661
            rcases Nat.lt_or_ge 13169345857 n with h12 | h12
            · -- n > 13169345857
              exact RamareSaouter2003.prime_interval_nat_ladder_c00096 n (by omega) (by omega)
            · -- n <= 13169345857
              exact RamareSaouter2003.prime_interval_nat_ladder_c00095 n (by omega) (by omega)
          · -- n <= 13140807661
            exact RamareSaouter2003.prime_interval_nat_ladder_c00094 n (by omega) (by omega)
      · -- n <= 13112334049
        rcases Nat.lt_or_ge 13027299713 n with h8 | h8
        · -- n > 13027299713
          rcases Nat.lt_or_ge 13055580289 n with h10 | h10
          · -- n > 13055580289
            rcases Nat.lt_or_ge 13083925039 n with h12 | h12
            · -- n > 13083925039
              exact RamareSaouter2003.prime_interval_nat_ladder_c00093 n (by omega) (by omega)
            · -- n <= 13083925039
              exact RamareSaouter2003.prime_interval_nat_ladder_c00092 n (by omega) (by omega)
          · -- n <= 13055580289
            exact RamareSaouter2003.prime_interval_nat_ladder_c00091 n (by omega) (by omega)
        · -- n <= 13027299713
          rcases Nat.lt_or_ge 12970930559 n with h10 | h10
          · -- n > 12970930559
            rcases Nat.lt_or_ge 12999083183 n with h12 | h12
            · -- n > 12999083183
              exact RamareSaouter2003.prime_interval_nat_ladder_c00090 n (by omega) (by omega)
            · -- n <= 12999083183
              exact RamareSaouter2003.prime_interval_nat_ladder_c00089 n (by omega) (by omega)
          · -- n <= 12970930559
            exact RamareSaouter2003.prime_interval_nat_ladder_c00088 n (by omega) (by omega)
    · -- n <= 12942841669
      rcases Nat.lt_or_ge 12775638649 n with h6 | h6
      · -- n > 12775638649
        rcases Nat.lt_or_ge 12858956057 n with h8 | h8
        · -- n > 12858956057
          rcases Nat.lt_or_ge 12886854553 n with h10 | h10
          · -- n > 12886854553
            rcases Nat.lt_or_ge 12914816417 n with h12 | h12
            · -- n > 12914816417
              exact RamareSaouter2003.prime_interval_nat_ladder_c00087 n (by omega) (by omega)
            · -- n <= 12914816417
              exact RamareSaouter2003.prime_interval_nat_ladder_c00086 n (by omega) (by omega)
          · -- n <= 12886854553
            exact RamareSaouter2003.prime_interval_nat_ladder_c00085 n (by omega) (by omega)
        · -- n <= 12858956057
          rcases Nat.lt_or_ge 12803348237 n with h10 | h10
          · -- n > 12803348237
            rcases Nat.lt_or_ge 12831120647 n with h12 | h12
            · -- n > 12831120647
              exact RamareSaouter2003.prime_interval_nat_ladder_c00084 n (by omega) (by omega)
            · -- n <= 12831120647
              exact RamareSaouter2003.prime_interval_nat_ladder_c00083 n (by omega) (by omega)
          · -- n <= 12803348237
            exact RamareSaouter2003.prime_interval_nat_ladder_c00082 n (by omega) (by omega)
      · -- n <= 12775638649
        rcases Nat.lt_or_ge 12692885567 n with h8 | h8
        · -- n > 12692885567
          rcases Nat.lt_or_ge 12720407501 n with h10 | h10
          · -- n > 12720407501
            rcases Nat.lt_or_ge 12747991819 n with h12 | h12
            · -- n > 12747991819
              exact RamareSaouter2003.prime_interval_nat_ladder_c00081 n (by omega) (by omega)
            · -- n <= 12747991819
              exact RamareSaouter2003.prime_interval_nat_ladder_c00080 n (by omega) (by omega)
          · -- n <= 12720407501
            exact RamareSaouter2003.prime_interval_nat_ladder_c00079 n (by omega) (by omega)
        · -- n <= 12692885567
          rcases Nat.lt_or_ge 12638028443 n with h10 | h10
          · -- n > 12638028443
            rcases Nat.lt_or_ge 12665425891 n with h12 | h12
            · -- n > 12665425891
              exact RamareSaouter2003.prime_interval_nat_ladder_c00078 n (by omega) (by omega)
            · -- n <= 12665425891
              exact RamareSaouter2003.prime_interval_nat_ladder_c00077 n (by omega) (by omega)
          · -- n <= 12638028443
            exact RamareSaouter2003.prime_interval_nat_ladder_c00076 n (by omega) (by omega)
  · -- n <= 12610692923
    rcases Nat.lt_or_ge 12260903003 n with h4 | h4
    · -- n > 12260903003
      rcases Nat.lt_or_ge 12421066633 n with h6 | h6
      · -- n > 12421066633
        rcases Nat.lt_or_ge 12501967319 n with h8 | h8
        · -- n > 12501967319
          rcases Nat.lt_or_ge 12556207099 n with h10 | h10
          · -- n > 12556207099
            rcases Nat.lt_or_ge 12583419137 n with h12 | h12
            · -- n > 12583419137
              exact RamareSaouter2003.prime_interval_nat_ladder_c00075 n (by omega) (by omega)
            · -- n <= 12583419137
              exact RamareSaouter2003.prime_interval_nat_ladder_c00074 n (by omega) (by omega)
          · -- n <= 12556207099
            rcases Nat.lt_or_ge 12529056541 n with h12 | h12
            · -- n > 12529056541
              exact RamareSaouter2003.prime_interval_nat_ladder_c00073 n (by omega) (by omega)
            · -- n <= 12529056541
              exact RamareSaouter2003.prime_interval_nat_ladder_c00072 n (by omega) (by omega)
        · -- n <= 12501967319
          rcases Nat.lt_or_ge 12447972517 n with h10 | h10
          · -- n > 12447972517
            rcases Nat.lt_or_ge 12474939401 n with h12 | h12
            · -- n > 12474939401
              exact RamareSaouter2003.prime_interval_nat_ladder_c00071 n (by omega) (by omega)
            · -- n <= 12474939401
              exact RamareSaouter2003.prime_interval_nat_ladder_c00070 n (by omega) (by omega)
          · -- n <= 12447972517
            exact RamareSaouter2003.prime_interval_nat_ladder_c00069 n (by omega) (by omega)
      · -- n <= 12421066633
        rcases Nat.lt_or_ge 12340713107 n with h8 | h8
        · -- n > 12340713107
          rcases Nat.lt_or_ge 12367437037 n with h10 | h10
          · -- n > 12367437037
            rcases Nat.lt_or_ge 12394221491 n with h12 | h12
            · -- n > 12394221491
              exact RamareSaouter2003.prime_interval_nat_ladder_c00068 n (by omega) (by omega)
            · -- n <= 12394221491
              exact RamareSaouter2003.prime_interval_nat_ladder_c00067 n (by omega) (by omega)
          · -- n <= 12367437037
            exact RamareSaouter2003.prime_interval_nat_ladder_c00066 n (by omega) (by omega)
        · -- n <= 12340713107
          rcases Nat.lt_or_ge 12287446181 n with h10 | h10
          · -- n > 12287446181
            rcases Nat.lt_or_ge 12314049533 n with h12 | h12
            · -- n > 12314049533
              exact RamareSaouter2003.prime_interval_nat_ladder_c00065 n (by omega) (by omega)
            · -- n <= 12314049533
              exact RamareSaouter2003.prime_interval_nat_ladder_c00064 n (by omega) (by omega)
          · -- n <= 12287446181
            exact RamareSaouter2003.prime_interval_nat_ladder_c00063 n (by omega) (by omega)
    · -- n <= 12260903003
      rcases Nat.lt_or_ge 12102897629 n with h6 | h6
      · -- n > 12102897629
        rcases Nat.lt_or_ge 12181632409 n with h8 | h8
        · -- n > 12181632409
          rcases Nat.lt_or_ge 12207996217 n with h10 | h10
          · -- n > 12207996217
            rcases Nat.lt_or_ge 12234419711 n with h12 | h12
            · -- n > 12234419711
              exact RamareSaouter2003.prime_interval_nat_ladder_c00062 n (by omega) (by omega)
            · -- n <= 12234419711
              exact RamareSaouter2003.prime_interval_nat_ladder_c00061 n (by omega) (by omega)
          · -- n <= 12207996217
            exact RamareSaouter2003.prime_interval_nat_ladder_c00060 n (by omega) (by omega)
        · -- n <= 12181632409
          rcases Nat.lt_or_ge 12129083287 n with h10 | h10
          · -- n > 12129083287
            rcases Nat.lt_or_ge 12155328197 n with h12 | h12
            · -- n > 12155328197
              exact RamareSaouter2003.prime_interval_nat_ladder_c00059 n (by omega) (by omega)
            · -- n <= 12155328197
              exact RamareSaouter2003.prime_interval_nat_ladder_c00058 n (by omega) (by omega)
          · -- n <= 12129083287
            exact RamareSaouter2003.prime_interval_nat_ladder_c00057 n (by omega) (by omega)
      · -- n <= 12102897629
        rcases Nat.lt_or_ge 12024694751 n with h8 | h8
        · -- n > 12024694751
          rcases Nat.lt_or_ge 12050703499 n with h10 | h10
          · -- n > 12050703499
            rcases Nat.lt_or_ge 12076771081 n with h12 | h12
            · -- n > 12076771081
              exact RamareSaouter2003.prime_interval_nat_ladder_c00056 n (by omega) (by omega)
            · -- n <= 12076771081
              exact RamareSaouter2003.prime_interval_nat_ladder_c00055 n (by omega) (by omega)
          · -- n <= 12050703499
            exact RamareSaouter2003.prime_interval_nat_ladder_c00054 n (by omega) (by omega)
        · -- n <= 12024694751
          rcases Nat.lt_or_ge 11972853197 n with h10 | h10
          · -- n > 11972853197
            rcases Nat.lt_or_ge 11998744697 n with h12 | h12
            · -- n > 11998744697
              exact RamareSaouter2003.prime_interval_nat_ladder_c00053 n (by omega) (by omega)
            · -- n <= 11998744697
              exact RamareSaouter2003.prime_interval_nat_ladder_c00052 n (by omega) (by omega)
          · -- n <= 11972853197
            exact RamareSaouter2003.prime_interval_nat_ladder_c00051 n (by omega) (by omega)
