-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_sgrp4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:09:14.538025+00:00
-- url     : https://prove2.me/submissions/5155f67c-6141-4859-a97e-9edaca81f3a9

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp133
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp134
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp135
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp136
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp137
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp138
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp139
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp140
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp141
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp142
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp143
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp144
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp145
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp146
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp147
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp148
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp149
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp150
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp151
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp152
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp153
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp154
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp155
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp156
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp157
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp158
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp159
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp160
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp161
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp162
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp163
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp164
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp165
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp166
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp167
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp168
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp169
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp170
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp171
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp172
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp173
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp174
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp175
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp176

theorem solution (n : Nat)
    (hn : 286750217619026779 < n) (hupper : n <= 10 ^ (20 : Nat)) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 6214769977508183639 n with h2 | h2
  · -- n > 6214769977508183639
    rcases Nat.lt_or_ge 26882311053914850133 n with h4 | h4
    · -- n > 26882311053914850133
      rcases Nat.lt_or_ge 48896242901857136909 n with h6 | h6
      · -- n > 48896242901857136909
        rcases Nat.lt_or_ge 70010134047899070677 n with h8 | h8
        · -- n > 70010134047899070677
          rcases Nat.lt_or_ge 78908309765868443269 n with h10 | h10
          · -- n > 78908309765868443269
            rcases Nat.lt_or_ge 88937429173397375471 n with h12 | h12
            · -- n > 88937429173397375471
              exact RamareSaouter2003.prime_interval_nat_ladder_grp176 n (by omega) hupper
            · -- n <= 88937429173397375471
              exact RamareSaouter2003.prime_interval_nat_ladder_grp175 n (by omega) (by omega)
          · -- n <= 78908309765868443269
            exact RamareSaouter2003.prime_interval_nat_ladder_grp174 n (by omega) (by omega)
        · -- n <= 70010134047899070677
          rcases Nat.lt_or_ge 55110872013924363761 n with h10 | h10
          · -- n > 55110872013924363761
            rcases Nat.lt_or_ge 62115373307991419869 n with h12 | h12
            · -- n > 62115373307991419869
              exact RamareSaouter2003.prime_interval_nat_ladder_grp173 n (by omega) (by omega)
            · -- n <= 62115373307991419869
              exact RamareSaouter2003.prime_interval_nat_ladder_grp172 n (by omega) (by omega)
          · -- n <= 55110872013924363761
            exact RamareSaouter2003.prime_interval_nat_ladder_grp171 n (by omega) (by omega)
      · -- n <= 48896242901857136909
        rcases Nat.lt_or_ge 34149953953884191081 n with h8 | h8
        · -- n > 34149953953884191081
          rcases Nat.lt_or_ge 38490349635789503129 n with h10 | h10
          · -- n > 38490349635789503129
            rcases Nat.lt_or_ge 43382410637006540717 n with h12 | h12
            · -- n > 43382410637006540717
              exact RamareSaouter2003.prime_interval_nat_ladder_grp170 n (by omega) (by omega)
            · -- n <= 43382410637006540717
              exact RamareSaouter2003.prime_interval_nat_ladder_grp169 n (by omega) (by omega)
          · -- n <= 38490349635789503129
            exact RamareSaouter2003.prime_interval_nat_ladder_grp168 n (by omega) (by omega)
        · -- n <= 34149953953884191081
          rcases Nat.lt_or_ge 30299003920194604927 n with h10 | h10
          · -- n > 30299003920194604927
            exact RamareSaouter2003.prime_interval_nat_ladder_grp167 n (by omega) (by omega)
          · -- n <= 30299003920194604927
            exact RamareSaouter2003.prime_interval_nat_ladder_grp166 n (by omega) (by omega)
    · -- n <= 26882311053914850133
      rcases Nat.lt_or_ge 12423819217158574193 n with h6 | h6
      · -- n > 12423819217158574193
        rcases Nat.lt_or_ge 18775057895451734561 n with h8 | h8
        · -- n > 18775057895451734561
          rcases Nat.lt_or_ge 21161333045580742687 n with h10 | h10
          · -- n > 21161333045580742687
            rcases Nat.lt_or_ge 23850902211042336817 n with h12 | h12
            · -- n > 23850902211042336817
              exact RamareSaouter2003.prime_interval_nat_ladder_grp165 n (by omega) (by omega)
            · -- n <= 23850902211042336817
              exact RamareSaouter2003.prime_interval_nat_ladder_grp164 n (by omega) (by omega)
          · -- n <= 21161333045580742687
            exact RamareSaouter2003.prime_interval_nat_ladder_grp163 n (by omega) (by omega)
        · -- n <= 18775057895451734561
          rcases Nat.lt_or_ge 14269908471619535531 n with h10 | h10
          · -- n > 14269908471619535531
            rcases Nat.lt_or_ge 16390314104476856209 n with h12 | h12
            · -- n > 16390314104476856209
              exact RamareSaouter2003.prime_interval_nat_ladder_grp162 n (by omega) (by omega)
            · -- n <= 16390314104476856209
              exact RamareSaouter2003.prime_interval_nat_ladder_grp161 n (by omega) (by omega)
          · -- n <= 14269908471619535531
            exact RamareSaouter2003.prime_interval_nat_ladder_grp160 n (by omega) (by omega)
      · -- n <= 12423819217158574193
        rcases Nat.lt_or_ge 8198927391296255473 n with h8 | h8
        · -- n > 8198927391296255473
          rcases Nat.lt_or_ge 9417226134267899261 n with h10 | h10
          · -- n > 9417226134267899261
            rcases Nat.lt_or_ge 10816557704663328019 n with h12 | h12
            · -- n > 10816557704663328019
              exact RamareSaouter2003.prime_interval_nat_ladder_grp159 n (by omega) (by omega)
            · -- n <= 10816557704663328019
              exact RamareSaouter2003.prime_interval_nat_ladder_grp158 n (by omega) (by omega)
          · -- n <= 9417226134267899261
            exact RamareSaouter2003.prime_interval_nat_ladder_grp157 n (by omega) (by omega)
        · -- n <= 8198927391296255473
          rcases Nat.lt_or_ge 7138238304410545217 n with h10 | h10
          · -- n > 7138238304410545217
            exact RamareSaouter2003.prime_interval_nat_ladder_grp156 n (by omega) (by omega)
          · -- n <= 7138238304410545217
            exact RamareSaouter2003.prime_interval_nat_ladder_grp155 n (by omega) (by omega)
  · -- n <= 6214769977508183639
    rcases Nat.lt_or_ge 1353944432269289611 n with h4 | h4
    · -- n > 1353944432269289611
      rcases Nat.lt_or_ge 2706634033163334233 n with h6 | h6
      · -- n > 2706634033163334233
        rcases Nat.lt_or_ge 4101353957833713881 n with h8 | h8
        · -- n > 4101353957833713881
          rcases Nat.lt_or_ge 4710784340673854327 n with h10 | h10
          · -- n > 4710784340673854327
            rcases Nat.lt_or_ge 5410770793340726459 n with h12 | h12
            · -- n > 5410770793340726459
              exact RamareSaouter2003.prime_interval_nat_ladder_grp154 n (by omega) (by omega)
            · -- n <= 5410770793340726459
              exact RamareSaouter2003.prime_interval_nat_ladder_grp153 n (by omega) (by omega)
          · -- n <= 4710784340673854327
            exact RamareSaouter2003.prime_interval_nat_ladder_grp152 n (by omega) (by omega)
        · -- n <= 4101353957833713881
          rcases Nat.lt_or_ge 3108818837989423529 n with h10 | h10
          · -- n > 3108818837989423529
            rcases Nat.lt_or_ge 3570765072310602017 n with h12 | h12
            · -- n > 3570765072310602017
              exact RamareSaouter2003.prime_interval_nat_ladder_grp151 n (by omega) (by omega)
            · -- n <= 3570765072310602017
              exact RamareSaouter2003.prime_interval_nat_ladder_grp150 n (by omega) (by omega)
          · -- n <= 3108818837989423529
            exact RamareSaouter2003.prime_interval_nat_ladder_grp149 n (by omega) (by omega)
      · -- n <= 2706634033163334233
        rcases Nat.lt_or_ge 1786208619689263597 n with h8 | h8
        · -- n > 1786208619689263597
          rcases Nat.lt_or_ge 2051624730942508333 n with h10 | h10
          · -- n > 2051624730942508333
            rcases Nat.lt_or_ge 2356479914408562661 n with h12 | h12
            · -- n > 2356479914408562661
              exact RamareSaouter2003.prime_interval_nat_ladder_grp148 n (by omega) (by omega)
            · -- n <= 2356479914408562661
              exact RamareSaouter2003.prime_interval_nat_ladder_grp147 n (by omega) (by omega)
          · -- n <= 2051624730942508333
            exact RamareSaouter2003.prime_interval_nat_ladder_grp146 n (by omega) (by omega)
        · -- n <= 1786208619689263597
          rcases Nat.lt_or_ge 1555129419536567443 n with h10 | h10
          · -- n > 1555129419536567443
            exact RamareSaouter2003.prime_interval_nat_ladder_grp145 n (by omega) (by omega)
          · -- n <= 1555129419536567443
            exact RamareSaouter2003.prime_interval_nat_ladder_grp144 n (by omega) (by omega)
    · -- n <= 1353944432269289611
      rcases Nat.lt_or_ge 581391753836179799 n with h6 | h6
      · -- n > 581391753836179799
        rcases Nat.lt_or_ge 888481536827254001 n with h8 | h8
        · -- n > 888481536827254001
          rcases Nat.lt_or_ge 1023391151980165547 n with h10 | h10
          · -- n > 1023391151980165547
            rcases Nat.lt_or_ge 1178786480577465181 n with h12 | h12
            · -- n > 1178786480577465181
              exact RamareSaouter2003.prime_interval_nat_ladder_grp143 n (by omega) (by omega)
            · -- n <= 1178786480577465181
              exact RamareSaouter2003.prime_interval_nat_ladder_grp142 n (by omega) (by omega)
          · -- n <= 1023391151980165547
            exact RamareSaouter2003.prime_interval_nat_ladder_grp141 n (by omega) (by omega)
        · -- n <= 888481536827254001
          rcases Nat.lt_or_ge 669672189073886627 n with h10 | h10
          · -- n > 669672189073886627
            rcases Nat.lt_or_ge 771356764495307657 n with h12 | h12
            · -- n > 771356764495307657
              exact RamareSaouter2003.prime_interval_nat_ladder_grp140 n (by omega) (by omega)
            · -- n <= 771356764495307657
              exact RamareSaouter2003.prime_interval_nat_ladder_grp139 n (by omega) (by omega)
          · -- n <= 669672189073886627
            exact RamareSaouter2003.prime_interval_nat_ladder_grp138 n (by omega) (by omega)
      · -- n <= 581391753836179799
        rcases Nat.lt_or_ge 380443069540112779 n with h8 | h8
        · -- n > 380443069540112779
          rcases Nat.lt_or_ge 438210345612193751 n with h10 | h10
          · -- n > 438210345612193751
            rcases Nat.lt_or_ge 504749525047989457 n with h12 | h12
            · -- n > 504749525047989457
              exact RamareSaouter2003.prime_interval_nat_ladder_grp137 n (by omega) (by omega)
            · -- n <= 504749525047989457
              exact RamareSaouter2003.prime_interval_nat_ladder_grp136 n (by omega) (by omega)
          · -- n <= 438210345612193751
            exact RamareSaouter2003.prime_interval_nat_ladder_grp135 n (by omega) (by omega)
        · -- n <= 380443069540112779
          rcases Nat.lt_or_ge 330290864187526579 n with h10 | h10
          · -- n > 330290864187526579
            exact RamareSaouter2003.prime_interval_nat_ladder_grp134 n (by omega) (by omega)
          · -- n <= 330290864187526579
            exact RamareSaouter2003.prime_interval_nat_ladder_grp133 n (by omega) (by omega)
