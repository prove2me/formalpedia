-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp083
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T09:14:10.237811+00:00
-- url     : https://prove2.me/submissions/9587344c-b9ae-400a-a450-5327842c28fa

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04101
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04102
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04103
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04104
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04105
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04106
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04107
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04108
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04109
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04110
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04111
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04112
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04113
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04114
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04115
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04116
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04117
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04118
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04119
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04120
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04121
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04122
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04123
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04124
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04125
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04126
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04127
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04128
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04129
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04130
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04131
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04132
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04133
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04134
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04135
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04136
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04137
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04138
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04139
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04140
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04141
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04142
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04143
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04144
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04145
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04146
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04147
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04148
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04149
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04150

theorem solution (n : Nat)
    (hn : 244566045604369 < n) (hupper : n <= 281681085386551) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 262468786757809 n with h2 | h2
  · -- n > 262468786757809
    rcases Nat.lt_or_ge 271521400397603 n with h4 | h4
    · -- n > 271521400397603
      rcases Nat.lt_or_ge 276164219716117 n with h6 | h6
      · -- n > 276164219716117
        rcases Nat.lt_or_ge 278515057424507 n with h8 | h8
        · -- n > 278515057424507
          rcases Nat.lt_or_ge 280093139667161 n with h10 | h10
          · -- n > 280093139667161
            rcases Nat.lt_or_ge 280886115432019 n with h12 | h12
            · -- n > 280886115432019
              exact RamareSaouter2003.prime_interval_nat_ladder_c04150 n (by omega) (by omega)
            · -- n <= 280886115432019
              exact RamareSaouter2003.prime_interval_nat_ladder_c04149 n (by omega) (by omega)
          · -- n <= 280093139667161
            rcases Nat.lt_or_ge 279303457103221 n with h12 | h12
            · -- n > 279303457103221
              exact RamareSaouter2003.prime_interval_nat_ladder_c04148 n (by omega) (by omega)
            · -- n <= 279303457103221
              exact RamareSaouter2003.prime_interval_nat_ladder_c04147 n (by omega) (by omega)
        · -- n <= 278515057424507
          rcases Nat.lt_or_ge 276945659666323 n with h10 | h10
          · -- n > 276945659666323
            rcases Nat.lt_or_ge 277729270683973 n with h12 | h12
            · -- n > 277729270683973
              exact RamareSaouter2003.prime_interval_nat_ladder_c04146 n (by omega) (by omega)
            · -- n <= 277729270683973
              exact RamareSaouter2003.prime_interval_nat_ladder_c04145 n (by omega) (by omega)
          · -- n <= 276945659666323
            exact RamareSaouter2003.prime_interval_nat_ladder_c04144 n (by omega) (by omega)
      · -- n <= 276164219716117
        rcases Nat.lt_or_ge 273832578188401 n with h8 | h8
        · -- n > 273832578188401
          rcases Nat.lt_or_ge 274607334297577 n with h10 | h10
          · -- n > 274607334297577
            rcases Nat.lt_or_ge 275384546384771 n with h12 | h12
            · -- n > 275384546384771
              exact RamareSaouter2003.prime_interval_nat_ladder_c04143 n (by omega) (by omega)
            · -- n <= 275384546384771
              exact RamareSaouter2003.prime_interval_nat_ladder_c04142 n (by omega) (by omega)
          · -- n <= 274607334297577
            exact RamareSaouter2003.prime_interval_nat_ladder_c04141 n (by omega) (by omega)
        · -- n <= 273832578188401
          rcases Nat.lt_or_ge 272289945502807 n with h10 | h10
          · -- n > 272289945502807
            rcases Nat.lt_or_ge 273059873719499 n with h12 | h12
            · -- n > 273059873719499
              exact RamareSaouter2003.prime_interval_nat_ladder_c04140 n (by omega) (by omega)
            · -- n <= 273059873719499
              exact RamareSaouter2003.prime_interval_nat_ladder_c04139 n (by omega) (by omega)
          · -- n <= 272289945502807
            exact RamareSaouter2003.prime_interval_nat_ladder_c04138 n (by omega) (by omega)
    · -- n <= 271521400397603
      rcases Nat.lt_or_ge 266955779028073 n with h6 | h6
      · -- n > 266955779028073
        rcases Nat.lt_or_ge 269228286878269 n with h8 | h8
        · -- n > 269228286878269
          rcases Nat.lt_or_ge 269990492846461 n with h10 | h10
          · -- n > 269990492846461
            rcases Nat.lt_or_ge 270754895135423 n with h12 | h12
            · -- n > 270754895135423
              exact RamareSaouter2003.prime_interval_nat_ladder_c04137 n (by omega) (by omega)
            · -- n <= 270754895135423
              exact RamareSaouter2003.prime_interval_nat_ladder_c04136 n (by omega) (by omega)
          · -- n <= 269990492846461
            exact RamareSaouter2003.prime_interval_nat_ladder_c04135 n (by omega) (by omega)
        · -- n <= 269228286878269
          rcases Nat.lt_or_ge 267710836869823 n with h10 | h10
          · -- n > 267710836869823
            rcases Nat.lt_or_ge 268468567376957 n with h12 | h12
            · -- n > 268468567376957
              exact RamareSaouter2003.prime_interval_nat_ladder_c04134 n (by omega) (by omega)
            · -- n <= 268468567376957
              exact RamareSaouter2003.prime_interval_nat_ladder_c04133 n (by omega) (by omega)
          · -- n <= 267710836869823
            exact RamareSaouter2003.prime_interval_nat_ladder_c04132 n (by omega) (by omega)
      · -- n <= 266955779028073
        rcases Nat.lt_or_ge 264703738750069 n with h8 | h8
        · -- n > 264703738750069
          rcases Nat.lt_or_ge 265452119844473 n with h10 | h10
          · -- n > 265452119844473
            rcases Nat.lt_or_ge 266202700964891 n with h12 | h12
            · -- n > 266202700964891
              exact RamareSaouter2003.prime_interval_nat_ladder_c04131 n (by omega) (by omega)
            · -- n <= 266202700964891
              exact RamareSaouter2003.prime_interval_nat_ladder_c04130 n (by omega) (by omega)
          · -- n <= 265452119844473
            exact RamareSaouter2003.prime_interval_nat_ladder_c04129 n (by omega) (by omega)
        · -- n <= 264703738750069
          rcases Nat.lt_or_ge 263211863870777 n with h10 | h10
          · -- n > 263211863870777
            rcases Nat.lt_or_ge 263956477411189 n with h12 | h12
            · -- n > 263956477411189
              exact RamareSaouter2003.prime_interval_nat_ladder_c04128 n (by omega) (by omega)
            · -- n <= 263956477411189
              exact RamareSaouter2003.prime_interval_nat_ladder_c04127 n (by omega) (by omega)
          · -- n <= 263211863870777
            exact RamareSaouter2003.prime_interval_nat_ladder_c04126 n (by omega) (by omega)
  · -- n <= 262468786757809
    rcases Nat.lt_or_ge 253001615553581 n with h4 | h4
    · -- n > 253001615553581
      rcases Nat.lt_or_ge 257327587363541 n with h6 | h6
      · -- n > 257327587363541
        rcases Nat.lt_or_ge 259518292847161 n with h8 | h8
        · -- n > 259518292847161
          rcases Nat.lt_or_ge 260989403968913 n with h10 | h10
          · -- n > 260989403968913
            rcases Nat.lt_or_ge 261727828371523 n with h12 | h12
            · -- n > 261727828371523
              exact RamareSaouter2003.prime_interval_nat_ladder_c04125 n (by omega) (by omega)
            · -- n <= 261727828371523
              exact RamareSaouter2003.prime_interval_nat_ladder_c04124 n (by omega) (by omega)
          · -- n <= 260989403968913
            rcases Nat.lt_or_ge 260252634755849 n with h12 | h12
            · -- n > 260252634755849
              exact RamareSaouter2003.prime_interval_nat_ladder_c04123 n (by omega) (by omega)
            · -- n <= 260252634755849
              exact RamareSaouter2003.prime_interval_nat_ladder_c04122 n (by omega) (by omega)
        · -- n <= 259518292847161
          rcases Nat.lt_or_ge 258055549169129 n with h10 | h10
          · -- n > 258055549169129
            rcases Nat.lt_or_ge 258786147197861 n with h12 | h12
            · -- n > 258786147197861
              exact RamareSaouter2003.prime_interval_nat_ladder_c04121 n (by omega) (by omega)
            · -- n <= 258786147197861
              exact RamareSaouter2003.prime_interval_nat_ladder_c04120 n (by omega) (by omega)
          · -- n <= 258055549169129
            exact RamareSaouter2003.prime_interval_nat_ladder_c04119 n (by omega) (by omega)
      · -- n <= 257327587363541
        rcases Nat.lt_or_ge 255156104471267 n with h8 | h8
        · -- n > 255156104471267
          rcases Nat.lt_or_ge 255878078256433 n with h10 | h10
          · -- n > 255878078256433
            rcases Nat.lt_or_ge 256602193292299 n with h12 | h12
            · -- n > 256602193292299
              exact RamareSaouter2003.prime_interval_nat_ladder_c04118 n (by omega) (by omega)
            · -- n <= 256602193292299
              exact RamareSaouter2003.prime_interval_nat_ladder_c04117 n (by omega) (by omega)
          · -- n <= 255878078256433
            exact RamareSaouter2003.prime_interval_nat_ladder_c04116 n (by omega) (by omega)
        · -- n <= 255156104471267
          rcases Nat.lt_or_ge 253717733535457 n with h10 | h10
          · -- n > 253717733535457
            rcases Nat.lt_or_ge 254435980315147 n with h12 | h12
            · -- n > 254435980315147
              exact RamareSaouter2003.prime_interval_nat_ladder_c04115 n (by omega) (by omega)
            · -- n <= 254435980315147
              exact RamareSaouter2003.prime_interval_nat_ladder_c04114 n (by omega) (by omega)
          · -- n <= 253717733535457
            exact RamareSaouter2003.prime_interval_nat_ladder_c04113 n (by omega) (by omega)
    · -- n <= 253001615553581
      rcases Nat.lt_or_ge 248748207495769 n with h6 | h6
      · -- n > 248748207495769
        rcases Nat.lt_or_ge 250866302722913 n with h8 | h8
        · -- n > 250866302722913
          rcases Nat.lt_or_ge 251575746170093 n with h10 | h10
          · -- n > 251575746170093
            rcases Nat.lt_or_ge 252287685020123 n with h12 | h12
            · -- n > 252287685020123
              exact RamareSaouter2003.prime_interval_nat_ladder_c04112 n (by omega) (by omega)
            · -- n <= 252287685020123
              exact RamareSaouter2003.prime_interval_nat_ladder_c04111 n (by omega) (by omega)
          · -- n <= 251575746170093
            exact RamareSaouter2003.prime_interval_nat_ladder_c04110 n (by omega) (by omega)
        · -- n <= 250866302722913
          rcases Nat.lt_or_ge 249452474188523 n with h10 | h10
          · -- n > 249452474188523
            rcases Nat.lt_or_ge 250158493405297 n with h12 | h12
            · -- n > 250158493405297
              exact RamareSaouter2003.prime_interval_nat_ladder_c04109 n (by omega) (by omega)
            · -- n <= 250158493405297
              exact RamareSaouter2003.prime_interval_nat_ladder_c04108 n (by omega) (by omega)
          · -- n <= 249452474188523
            exact RamareSaouter2003.prime_interval_nat_ladder_c04107 n (by omega) (by omega)
      · -- n <= 248748207495769
        rcases Nat.lt_or_ge 246648203861929 n with h8 | h8
        · -- n > 246648203861929
          rcases Nat.lt_or_ge 247346472225949 n with h10 | h10
          · -- n > 247346472225949
            rcases Nat.lt_or_ge 248046766832167 n with h12 | h12
            · -- n > 248046766832167
              exact RamareSaouter2003.prime_interval_nat_ladder_c04106 n (by omega) (by omega)
            · -- n <= 248046766832167
              exact RamareSaouter2003.prime_interval_nat_ladder_c04105 n (by omega) (by omega)
          · -- n <= 247346472225949
            exact RamareSaouter2003.prime_interval_nat_ladder_c04104 n (by omega) (by omega)
        · -- n <= 246648203861929
          rcases Nat.lt_or_ge 245258198519953 n with h10 | h10
          · -- n > 245258198519953
            rcases Nat.lt_or_ge 245952113870777 n with h12 | h12
            · -- n > 245952113870777
              exact RamareSaouter2003.prime_interval_nat_ladder_c04103 n (by omega) (by omega)
            · -- n <= 245952113870777
              exact RamareSaouter2003.prime_interval_nat_ladder_c04102 n (by omega) (by omega)
          · -- n <= 245258198519953
            exact RamareSaouter2003.prime_interval_nat_ladder_c04101 n (by omega) (by omega)
