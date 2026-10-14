-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp103
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T14:47:36.550012+00:00
-- url     : https://prove2.me/submissions/0a332654-8180-4a21-a330-7927d902e6a2

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05101
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05102
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05103
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05104
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05105
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05106
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05107
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05108
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05109
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05110
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05111
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05112
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05113
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05114
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05115
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05116
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05117
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05118
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05119
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05120
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05121
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05122
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05123
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05124
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05125
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05126
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05127
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05128
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05129
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05130
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05131
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05132
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05133
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05134
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05135
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05136
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05137
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05138
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05139
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05140
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05141
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05142
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05143
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05144
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05145
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05146
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05147
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05148
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05149
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05150

theorem solution (n : Nat)
    (hn : 4128840276810539 < n) (hupper : n <= 4755668462802073) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 4431176030707537 n with h2 | h2
  · -- n > 4431176030707537
    rcases Nat.lt_or_ge 4584066825754729 n with h4 | h4
    · -- n > 4584066825754729
      rcases Nat.lt_or_ge 4662484092893401 n with h6 | h6
      · -- n > 4662484092893401
        rcases Nat.lt_or_ge 4702196385529711 n with h8 | h8
        · -- n > 4702196385529711
          rcases Nat.lt_or_ge 4728857365504333 n with h10 | h10
          · -- n > 4728857365504333
            rcases Nat.lt_or_ge 4742245797926369 n with h12 | h12
            · -- n > 4742245797926369
              exact RamareSaouter2003.prime_interval_nat_ladder_c05150 n (by omega) (by omega)
            · -- n <= 4742245797926369
              exact RamareSaouter2003.prime_interval_nat_ladder_c05149 n (by omega) (by omega)
          · -- n <= 4728857365504333
            rcases Nat.lt_or_ge 4715507221761079 n with h12 | h12
            · -- n > 4715507221761079
              exact RamareSaouter2003.prime_interval_nat_ladder_c05148 n (by omega) (by omega)
            · -- n <= 4715507221761079
              exact RamareSaouter2003.prime_interval_nat_ladder_c05147 n (by omega) (by omega)
        · -- n <= 4702196385529711
          rcases Nat.lt_or_ge 4675684899839827 n with h10 | h10
          · -- n > 4675684899839827
            rcases Nat.lt_or_ge 4688922577776533 n with h12 | h12
            · -- n > 4688922577776533
              exact RamareSaouter2003.prime_interval_nat_ladder_c05146 n (by omega) (by omega)
            · -- n <= 4688922577776533
              exact RamareSaouter2003.prime_interval_nat_ladder_c05145 n (by omega) (by omega)
          · -- n <= 4675684899839827
            exact RamareSaouter2003.prime_interval_nat_ladder_c05144 n (by omega) (by omega)
      · -- n <= 4662484092893401
        rcases Nat.lt_or_ge 4623110328203291 n with h8 | h8
        · -- n > 4623110328203291
          rcases Nat.lt_or_ge 4636198119140233 n with h10 | h10
          · -- n > 4636198119140233
            rcases Nat.lt_or_ge 4649323773173951 n with h12 | h12
            · -- n > 4649323773173951
              exact RamareSaouter2003.prime_interval_nat_ladder_c05143 n (by omega) (by omega)
            · -- n <= 4649323773173951
              exact RamareSaouter2003.prime_interval_nat_ladder_c05142 n (by omega) (by omega)
          · -- n <= 4636198119140233
            exact RamareSaouter2003.prime_interval_nat_ladder_c05141 n (by omega) (by omega)
        · -- n <= 4623110328203291
          rcases Nat.lt_or_ge 4597042993188259 n with h10 | h10
          · -- n > 4597042993188259
            rcases Nat.lt_or_ge 4610058422869321 n with h12 | h12
            · -- n > 4610058422869321
              exact RamareSaouter2003.prime_interval_nat_ladder_c05140 n (by omega) (by omega)
            · -- n <= 4610058422869321
              exact RamareSaouter2003.prime_interval_nat_ladder_c05139 n (by omega) (by omega)
          · -- n <= 4597042993188259
            exact RamareSaouter2003.prime_interval_nat_ladder_c05138 n (by omega) (by omega)
    · -- n <= 4584066825754729
      rcases Nat.lt_or_ge 4506979744027597 n with h6 | h6
      · -- n > 4506979744027597
        rcases Nat.lt_or_ge 4545357705227147 n with h8 | h8
        · -- n > 4545357705227147
          rcases Nat.lt_or_ge 4558223920505951 n with h10 | h10
          · -- n > 4558223920505951
            rcases Nat.lt_or_ge 4571128601859619 n with h12 | h12
            · -- n > 4571128601859619
              exact RamareSaouter2003.prime_interval_nat_ladder_c05137 n (by omega) (by omega)
            · -- n <= 4571128601859619
              exact RamareSaouter2003.prime_interval_nat_ladder_c05136 n (by omega) (by omega)
          · -- n <= 4558223920505951
            exact RamareSaouter2003.prime_interval_nat_ladder_c05135 n (by omega) (by omega)
        · -- n <= 4545357705227147
          rcases Nat.lt_or_ge 4519740202517833 n with h10 | h10
          · -- n > 4519740202517833
            rcases Nat.lt_or_ge 4532524886542637 n with h12 | h12
            · -- n > 4532524886542637
              exact RamareSaouter2003.prime_interval_nat_ladder_c05134 n (by omega) (by omega)
            · -- n <= 4532524886542637
              exact RamareSaouter2003.prime_interval_nat_ladder_c05133 n (by omega) (by omega)
          · -- n <= 4519740202517833
            exact RamareSaouter2003.prime_interval_nat_ladder_c05132 n (by omega) (by omega)
      · -- n <= 4506979744027597
        rcases Nat.lt_or_ge 4468915566453563 n with h8 | h8
        · -- n > 4468915566453563
          rcases Nat.lt_or_ge 4481567167805183 n with h10 | h10
          · -- n > 4481567167805183
            rcases Nat.lt_or_ge 4494255291834809 n with h12 | h12
            · -- n > 4494255291834809
              exact RamareSaouter2003.prime_interval_nat_ladder_c05131 n (by omega) (by omega)
            · -- n <= 4494255291834809
              exact RamareSaouter2003.prime_interval_nat_ladder_c05130 n (by omega) (by omega)
          · -- n <= 4481567167805183
            exact RamareSaouter2003.prime_interval_nat_ladder_c05129 n (by omega) (by omega)
        · -- n <= 4468915566453563
          rcases Nat.lt_or_ge 4443720807000697 n with h10 | h10
          · -- n > 4443720807000697
            rcases Nat.lt_or_ge 4456299467448523 n with h12 | h12
            · -- n > 4456299467448523
              exact RamareSaouter2003.prime_interval_nat_ladder_c05128 n (by omega) (by omega)
            · -- n <= 4456299467448523
              exact RamareSaouter2003.prime_interval_nat_ladder_c05127 n (by omega) (by omega)
          · -- n <= 4443720807000697
            exact RamareSaouter2003.prime_interval_nat_ladder_c05126 n (by omega) (by omega)
  · -- n <= 4431176030707537
    rcases Nat.lt_or_ge 4271304040662937 n with h4 | h4
    · -- n > 4271304040662937
      rcases Nat.lt_or_ge 4344355922446363 n with h6 | h6
      · -- n > 4344355922446363
        rcases Nat.lt_or_ge 4381353490106101 n with h8 | h8
        · -- n > 4381353490106101
          rcases Nat.lt_or_ge 4406193570742151 n with h10 | h10
          · -- n > 4406193570742151
            rcases Nat.lt_or_ge 4418666666640911 n with h12 | h12
            · -- n > 4418666666640911
              exact RamareSaouter2003.prime_interval_nat_ladder_c05125 n (by omega) (by omega)
            · -- n <= 4418666666640911
              exact RamareSaouter2003.prime_interval_nat_ladder_c05124 n (by omega) (by omega)
          · -- n <= 4406193570742151
            rcases Nat.lt_or_ge 4393756134394217 n with h12 | h12
            · -- n > 4393756134394217
              exact RamareSaouter2003.prime_interval_nat_ladder_c05123 n (by omega) (by omega)
            · -- n <= 4393756134394217
              exact RamareSaouter2003.prime_interval_nat_ladder_c05122 n (by omega) (by omega)
        · -- n <= 4381353490106101
          rcases Nat.lt_or_ge 4356655833072443 n with h10 | h10
          · -- n > 4356655833072443
            rcases Nat.lt_or_ge 4368983837086387 n with h12 | h12
            · -- n > 4368983837086387
              exact RamareSaouter2003.prime_interval_nat_ladder_c05121 n (by omega) (by omega)
            · -- n <= 4368983837086387
              exact RamareSaouter2003.prime_interval_nat_ladder_c05120 n (by omega) (by omega)
          · -- n <= 4356655833072443
            exact RamareSaouter2003.prime_interval_nat_ladder_c05119 n (by omega) (by omega)
      · -- n <= 4344355922446363
        rcases Nat.lt_or_ge 4307679963375301 n with h8 | h8
        · -- n > 4307679963375301
          rcases Nat.lt_or_ge 4319874641061403 n with h10 | h10
          · -- n > 4319874641061403
            rcases Nat.lt_or_ge 4332090765682033 n with h12 | h12
            · -- n > 4332090765682033
              exact RamareSaouter2003.prime_interval_nat_ladder_c05118 n (by omega) (by omega)
            · -- n <= 4332090765682033
              exact RamareSaouter2003.prime_interval_nat_ladder_c05117 n (by omega) (by omega)
          · -- n <= 4319874641061403
            exact RamareSaouter2003.prime_interval_nat_ladder_c05116 n (by omega) (by omega)
        · -- n <= 4307679963375301
          rcases Nat.lt_or_ge 4283395324074677 n with h10 | h10
          · -- n > 4283395324074677
            rcases Nat.lt_or_ge 4295520083308379 n with h12 | h12
            · -- n > 4295520083308379
              exact RamareSaouter2003.prime_interval_nat_ladder_c05115 n (by omega) (by omega)
            · -- n <= 4295520083308379
              exact RamareSaouter2003.prime_interval_nat_ladder_c05114 n (by omega) (by omega)
          · -- n <= 4283395324074677
            exact RamareSaouter2003.prime_interval_nat_ladder_c05113 n (by omega) (by omega)
    · -- n <= 4271304040662937
      rcases Nat.lt_or_ge 4199467093489133 n with h6 | h6
      · -- n > 4199467093489133
        rcases Nat.lt_or_ge 4235234637475181 n with h8 | h8
        · -- n > 4235234637475181
          rcases Nat.lt_or_ge 4247222789123693 n with h10 | h10
          · -- n > 4247222789123693
            rcases Nat.lt_or_ge 4259245376408137 n with h12 | h12
            · -- n > 4259245376408137
              exact RamareSaouter2003.prime_interval_nat_ladder_c05112 n (by omega) (by omega)
            · -- n <= 4259245376408137
              exact RamareSaouter2003.prime_interval_nat_ladder_c05111 n (by omega) (by omega)
          · -- n <= 4247222789123693
            exact RamareSaouter2003.prime_interval_nat_ladder_c05110 n (by omega) (by omega)
        · -- n <= 4235234637475181
          rcases Nat.lt_or_ge 4211356143809831 n with h10 | h10
          · -- n > 4211356143809831
            rcases Nat.lt_or_ge 4223278500773609 n with h12 | h12
            · -- n > 4223278500773609
              exact RamareSaouter2003.prime_interval_nat_ladder_c05109 n (by omega) (by omega)
            · -- n <= 4223278500773609
              exact RamareSaouter2003.prime_interval_nat_ladder_c05108 n (by omega) (by omega)
          · -- n <= 4211356143809831
            exact RamareSaouter2003.prime_interval_nat_ladder_c05107 n (by omega) (by omega)
      · -- n <= 4199467093489133
        rcases Nat.lt_or_ge 4164004932187651 n with h8 | h8
        · -- n > 4164004932187651
          rcases Nat.lt_or_ge 4175791108343909 n with h10 | h10
          · -- n > 4175791108343909
            rcases Nat.lt_or_ge 4187613228265801 n with h12 | h12
            · -- n > 4187613228265801
              exact RamareSaouter2003.prime_interval_nat_ladder_c05106 n (by omega) (by omega)
            · -- n <= 4187613228265801
              exact RamareSaouter2003.prime_interval_nat_ladder_c05105 n (by omega) (by omega)
          · -- n <= 4175791108343909
            exact RamareSaouter2003.prime_interval_nat_ladder_c05104 n (by omega) (by omega)
        · -- n <= 4164004932187651
          rcases Nat.lt_or_ge 4140526170383107 n with h10 | h10
          · -- n > 4140526170383107
            rcases Nat.lt_or_ge 4152248812269641 n with h12 | h12
            · -- n > 4152248812269641
              exact RamareSaouter2003.prime_interval_nat_ladder_c05103 n (by omega) (by omega)
            · -- n <= 4152248812269641
              exact RamareSaouter2003.prime_interval_nat_ladder_c05102 n (by omega) (by omega)
          · -- n <= 4140526170383107
            exact RamareSaouter2003.prime_interval_nat_ladder_c05101 n (by omega) (by omega)
