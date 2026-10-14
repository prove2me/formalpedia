-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp163
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T12:16:34.367719+00:00
-- url     : https://prove2.me/submissions/0d28fe6a-4970-467d-b4d9-8283d711adf9

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08081
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08082
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08083
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08084
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08085
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08086
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08087
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08088
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08089
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08090
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08091
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08092
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08093
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08094
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08095
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08096
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08097
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08098
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08099
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08100
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08101
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08102
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08103
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08104
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08105
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08106
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08107
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08108
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08109
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08110
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08111
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08112
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08113
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08114
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08115
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08116
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08117
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08118
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08119
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08120
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08121
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08122
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08123
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08124
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08125
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08126
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08127
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08128
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08129

theorem solution (n : Nat)
    (hn : 18775057895451734561 < n) (hupper : n <= 21161333045580742687) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 19908196464981721081 n with h2 | h2
  · -- n > 19908196464981721081
    rcases Nat.lt_or_ge 20500159356730455377 n with h4 | h4
    · -- n > 20500159356730455377
      rcases Nat.lt_or_ge 20802709806618792907 n with h6 | h6
      · -- n > 20802709806618792907
        rcases Nat.lt_or_ge 20955655284235904429 n with h8 | h8
        · -- n > 20955655284235904429
          rcases Nat.lt_or_ge 21058243287586650287 n with h10 | h10
          · -- n > 21058243287586650287
            rcases Nat.lt_or_ge 21109725463711811519 n with h12 | h12
            · -- n > 21109725463711811519
              exact RamareSaouter2003.prime_interval_nat_ladder_c08129 n (by omega) (by omega)
            · -- n <= 21109725463711811519
              exact RamareSaouter2003.prime_interval_nat_ladder_c08128 n (by omega) (by omega)
          · -- n <= 21058243287586650287
            rcases Nat.lt_or_ge 21006886656155514547 n with h12 | h12
            · -- n > 21006886656155514547
              exact RamareSaouter2003.prime_interval_nat_ladder_c08127 n (by omega) (by omega)
            · -- n <= 21006886656155514547
              exact RamareSaouter2003.prime_interval_nat_ladder_c08126 n (by omega) (by omega)
        · -- n <= 20955655284235904429
          rcases Nat.lt_or_ge 20853567183749544679 n with h10 | h10
          · -- n > 20853567183749544679
            rcases Nat.lt_or_ge 20904549007018335287 n with h12 | h12
            · -- n > 20904549007018335287
              exact RamareSaouter2003.prime_interval_nat_ladder_c08125 n (by omega) (by omega)
            · -- n <= 20904549007018335287
              exact RamareSaouter2003.prime_interval_nat_ladder_c08124 n (by omega) (by omega)
          · -- n <= 20853567183749544679
            exact RamareSaouter2003.prime_interval_nat_ladder_c08123 n (by omega) (by omega)
      · -- n <= 20802709806618792907
        rcases Nat.lt_or_ge 20650880408147432291 n with h8 | h8
        · -- n > 20650880408147432291
          rcases Nat.lt_or_ge 20701366676882600609 n with h10 | h10
          · -- n > 20701366676882600609
            rcases Nat.lt_or_ge 20751976373731321853 n with h12 | h12
            · -- n > 20751976373731321853
              exact RamareSaouter2003.prime_interval_nat_ladder_c08122 n (by omega) (by omega)
            · -- n <= 20751976373731321853
              exact RamareSaouter2003.prime_interval_nat_ladder_c08121 n (by omega) (by omega)
          · -- n <= 20701366676882600609
            exact RamareSaouter2003.prime_interval_nat_ladder_c08120 n (by omega) (by omega)
        · -- n <= 20650880408147432291
          rcases Nat.lt_or_ge 20550276950302211309 n with h10 | h10
          · -- n > 20550276950302211309
            rcases Nat.lt_or_ge 20600517249577703989 n with h12 | h12
            · -- n > 20600517249577703989
              exact RamareSaouter2003.prime_interval_nat_ladder_c08119 n (by omega) (by omega)
            · -- n <= 20600517249577703989
              exact RamareSaouter2003.prime_interval_nat_ladder_c08118 n (by omega) (by omega)
          · -- n <= 20550276950302211309
            exact RamareSaouter2003.prime_interval_nat_ladder_c08117 n (by omega) (by omega)
    · -- n <= 20500159356730455377
      rcases Nat.lt_or_ge 20202009858562499431 n with h6 | h6
      · -- n > 20202009858562499431
        rcases Nat.lt_or_ge 20350538680026897061 n with h8 | h8
        · -- n > 20350538680026897061
          rcases Nat.lt_or_ge 20400290422580983769 n with h10 | h10
          · -- n > 20400290422580983769
            rcases Nat.lt_or_ge 20450163819679283149 n with h12 | h12
            · -- n > 20450163819679283149
              exact RamareSaouter2003.prime_interval_nat_ladder_c08116 n (by omega) (by omega)
            · -- n <= 20450163819679283149
              exact RamareSaouter2003.prime_interval_nat_ladder_c08115 n (by omega) (by omega)
          · -- n <= 20400290422580983769
            exact RamareSaouter2003.prime_interval_nat_ladder_c08114 n (by omega) (by omega)
        · -- n <= 20350538680026897061
          rcases Nat.lt_or_ge 20251398637915821913 n with h10 | h10
          · -- n > 20251398637915821913
            rcases Nat.lt_or_ge 20300908062602600677 n with h12 | h12
            · -- n > 20300908062602600677
              exact RamareSaouter2003.prime_interval_nat_ladder_c08113 n (by omega) (by omega)
            · -- n <= 20300908062602600677
              exact RamareSaouter2003.prime_interval_nat_ladder_c08112 n (by omega) (by omega)
          · -- n <= 20251398637915821913
            exact RamareSaouter2003.prime_interval_nat_ladder_c08111 n (by omega) (by omega)
      · -- n <= 20202009858562499431
        rcases Nat.lt_or_ge 20054564902125270739 n with h8 | h8
        · -- n > 20054564902125270739
          rcases Nat.lt_or_ge 20103593305727962651 n with h10 | h10
          · -- n > 20103593305727962651
            rcases Nat.lt_or_ge 20152741542781452617 n with h12 | h12
            · -- n > 20152741542781452617
              exact RamareSaouter2003.prime_interval_nat_ladder_c08110 n (by omega) (by omega)
            · -- n <= 20152741542781452617
              exact RamareSaouter2003.prime_interval_nat_ladder_c08109 n (by omega) (by omega)
          · -- n <= 20103593305727962651
            exact RamareSaouter2003.prime_interval_nat_ladder_c08108 n (by omega) (by omega)
        · -- n <= 20054564902125270739
          rcases Nat.lt_or_ge 19956866807941220207 n with h10 | h10
          · -- n > 19956866807941220207
            rcases Nat.lt_or_ge 20005656112839985043 n with h12 | h12
            · -- n > 20005656112839985043
              exact RamareSaouter2003.prime_interval_nat_ladder_c08107 n (by omega) (by omega)
            · -- n <= 20005656112839985043
              exact RamareSaouter2003.prime_interval_nat_ladder_c08106 n (by omega) (by omega)
          · -- n <= 19956866807941220207
            exact RamareSaouter2003.prime_interval_nat_ladder_c08105 n (by omega) (by omega)
  · -- n <= 19908196464981721081
    rcases Nat.lt_or_ge 19333326822782007677 n with h4 | h4
    · -- n > 19333326822782007677
      rcases Nat.lt_or_ge 19618656264385732231 n with h6 | h6
      · -- n > 19618656264385732231
        rcases Nat.lt_or_ge 19762895832041340943 n with h8 | h8
        · -- n > 19762895832041340943
          rcases Nat.lt_or_ge 19811211126812544247 n with h10 | h10
          · -- n > 19811211126812544247
            rcases Nat.lt_or_ge 19859644589391712657 n with h12 | h12
            · -- n > 19859644589391712657
              exact RamareSaouter2003.prime_interval_nat_ladder_c08104 n (by omega) (by omega)
            · -- n <= 19859644589391712657
              exact RamareSaouter2003.prime_interval_nat_ladder_c08103 n (by omega) (by omega)
          · -- n <= 19811211126812544247
            exact RamareSaouter2003.prime_interval_nat_ladder_c08102 n (by omega) (by omega)
        · -- n <= 19762895832041340943
          rcases Nat.lt_or_ge 19666618553342051789 n with h10 | h10
          · -- n > 19666618553342051789
            rcases Nat.lt_or_ge 19714698364651077257 n with h12 | h12
            · -- n > 19714698364651077257
              exact RamareSaouter2003.prime_interval_nat_ladder_c08101 n (by omega) (by omega)
            · -- n <= 19714698364651077257
              exact RamareSaouter2003.prime_interval_nat_ladder_c08100 n (by omega) (by omega)
          · -- n <= 19666618553342051789
            exact RamareSaouter2003.prime_interval_nat_ladder_c08099 n (by omega) (by omega)
      · -- n <= 19618656264385732231
        rcases Nat.lt_or_ge 19475469053840046497 n with h8 | h8
        · -- n > 19475469053840046497
          rcases Nat.lt_or_ge 19523081660931053659 n with h10 | h10
          · -- n > 19523081660931053659
            rcases Nat.lt_or_ge 19570810641821899091 n with h12 | h12
            · -- n > 19570810641821899091
              exact RamareSaouter2003.prime_interval_nat_ladder_c08098 n (by omega) (by omega)
            · -- n <= 19570810641821899091
              exact RamareSaouter2003.prime_interval_nat_ladder_c08097 n (by omega) (by omega)
          · -- n <= 19523081660931053659
            exact RamareSaouter2003.prime_interval_nat_ladder_c08096 n (by omega) (by omega)
        · -- n <= 19475469053840046497
          rcases Nat.lt_or_ge 19380592014423454669 n with h10 | h10
          · -- n > 19380592014423454669
            rcases Nat.lt_or_ge 19427972625769847999 n with h12 | h12
            · -- n > 19427972625769847999
              exact RamareSaouter2003.prime_interval_nat_ladder_c08095 n (by omega) (by omega)
            · -- n <= 19427972625769847999
              exact RamareSaouter2003.prime_interval_nat_ladder_c08094 n (by omega) (by omega)
          · -- n <= 19380592014423454669
            exact RamareSaouter2003.prime_interval_nat_ladder_c08093 n (by omega) (by omega)
    · -- n <= 19333326822782007677
      rcases Nat.lt_or_ge 19052147378853985679 n with h6 | h6
      · -- n > 19052147378853985679
        rcases Nat.lt_or_ge 19192221974047128581 n with h8 | h8
        · -- n > 19192221974047128581
          rcases Nat.lt_or_ge 19239142136050933897 n with h10 | h10
          · -- n > 19239142136050933897
            rcases Nat.lt_or_ge 19286176996967547851 n with h12 | h12
            · -- n > 19286176996967547851
              exact RamareSaouter2003.prime_interval_nat_ladder_c08092 n (by omega) (by omega)
            · -- n <= 19286176996967547851
              exact RamareSaouter2003.prime_interval_nat_ladder_c08091 n (by omega) (by omega)
          · -- n <= 19239142136050933897
            exact RamareSaouter2003.prime_interval_nat_ladder_c08090 n (by omega) (by omega)
        · -- n <= 19192221974047128581
          rcases Nat.lt_or_ge 19098725093069084563 n with h10 | h10
          · -- n > 19098725093069084563
            rcases Nat.lt_or_ge 19145416257832640681 n with h12 | h12
            · -- n > 19145416257832640681
              exact RamareSaouter2003.prime_interval_nat_ladder_c08089 n (by omega) (by omega)
            · -- n <= 19145416257832640681
              exact RamareSaouter2003.prime_interval_nat_ladder_c08088 n (by omega) (by omega)
          · -- n <= 19098725093069084563
            exact RamareSaouter2003.prime_interval_nat_ladder_c08087 n (by omega) (by omega)
      · -- n <= 19052147378853985679
        rcases Nat.lt_or_ge 18913095089184044599 n with h8 | h8
        · -- n > 18913095089184044599
          rcases Nat.lt_or_ge 18959332789237009159 n with h10 | h10
          · -- n > 18959332789237009159
            rcases Nat.lt_or_ge 19005683588241207313 n with h12 | h12
            · -- n > 19005683588241207313
              exact RamareSaouter2003.prime_interval_nat_ladder_c08086 n (by omega) (by omega)
            · -- n <= 19005683588241207313
              exact RamareSaouter2003.prime_interval_nat_ladder_c08085 n (by omega) (by omega)
          · -- n <= 18959332789237009159
            exact RamareSaouter2003.prime_interval_nat_ladder_c08084 n (by omega) (by omega)
        · -- n <= 18913095089184044599
          rcases Nat.lt_or_ge 18820958130482208907 n with h10 | h10
          · -- n > 18820958130482208907
            rcases Nat.lt_or_ge 18866970141263208539 n with h12 | h12
            · -- n > 18866970141263208539
              exact RamareSaouter2003.prime_interval_nat_ladder_c08083 n (by omega) (by omega)
            · -- n <= 18866970141263208539
              exact RamareSaouter2003.prime_interval_nat_ladder_c08082 n (by omega) (by omega)
          · -- n <= 18820958130482208907
            exact RamareSaouter2003.prime_interval_nat_ladder_c08081 n (by omega) (by omega)
