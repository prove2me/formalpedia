-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp04
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:42:50.831984+00:00
-- url     : https://prove2.me/submissions/d2e13e5e-4191-40c2-9779-d05057f65f81

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg148
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg149
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg150
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg151
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg152
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg153
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg154
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg155
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg156
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg157
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg158
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg159
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg160
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg161
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg162
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg163
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg164
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg165
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg166
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg167
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg168
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg169
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg170
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg171
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg172
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg173
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg174
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg175
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg176
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg177
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg178
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg179
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg180
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg181
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg182
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg183
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg184
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg185
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg186
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg187
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg188
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg189
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg190
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg191
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg192
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg193
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg194
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg195
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg196

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp04` (18797957278071626724802561 <= x < 25063941703624474117537793) from the 49 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg148` .. `WeakGoldbach.prime_in_4e18_window_proth_seg196`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 18797957278071626724802561 ≤ x) (hx : x < 25063941703624474117537793) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 21867010874499168540295169 with hc24 | hc24
  · rcases Nat.lt_or_ge x 20332484076056699213971457 with hc12 | hc12
    · rcases Nat.lt_or_ge x 19565220677072959062409217 with hc6 | hc6
      · rcases Nat.lt_or_ge x 19181588977079711684362241 with hc3 | hc3
        · rcases Nat.lt_or_ge x 18925834510593468626108417 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg148 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 19053711743291232387858433 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg149 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg150 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 19309466209408039539179521 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg151 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 19437343443865021905371137 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg152 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg153 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 19948852376538440859123713 with hc9 | hc9
        · rcases Nat.lt_or_ge x 19693097910351264963624961 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg154 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 19820975142081458492932097 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg155 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg156 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 20076729609975076434739201 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg157 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 20204606842584879266267137 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg158 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg159 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 21099747474512673784201217 with hc18 | hc18
      · rcases Nat.lt_or_ge x 20716115775786063801352193 with hc15 | hc15
        · rcases Nat.lt_or_ge x 20460361308912792650121217 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg160 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 20588238542595718830358529 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg161 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg162 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 20843993008448643191013377 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg163 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 20971870242201938115428353 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg164 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg165 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 21483379174752211766870017 with hc21 | hc21
        · rcases Nat.lt_or_ge x 21227624708635404615548929 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg166 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 21355501941825749586542593 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg167 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg168 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 21611256408153662970396673 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg169 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 21739133641414376685568001 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg170 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg171 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 23401537671710184843509761 with hc36 | hc36
    · rcases Nat.lt_or_ge x 22634274273271802459324417 with hc30 | hc30
      · rcases Nat.lt_or_ge x 22250642574017426895142913 with hc27 | hc27
        · rcases Nat.lt_or_ge x 21994888106246954255646721 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg172 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 22122765340440053831172097 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg173 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg174 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 22378519807366101540536321 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg175 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 22506397040538854325485569 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg176 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg177 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 23017905973159496721104897 with hc33 | hc33
        · rcases Nat.lt_or_ge x 22762151506831583337250817 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg178 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 22890028740109889238466561 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg179 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg180 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 23145783205382271459655681 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg181 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 23273660439680924151447553 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg182 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg183 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 24168801071503165553115137 with hc42 | hc42
      · rcases Nat.lt_or_ge x 23785169371457141616934913 with hc39 | hc39
        · rcases Nat.lt_or_ge x 23529414905393111023747073 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg184 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 23657292137299226413498369 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg185 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg186 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 23913046605157659983216641 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg187 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 24040923838576703372787713 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg188 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg189 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 24552432770951055163785217 with hc45 | hc45
        · rcases Nat.lt_or_ge x 24296678304376851175309313 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg190 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 24424555538358844518301697 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg191 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg192 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 24808187236874348268617729 with hc47 | hc47
          · rcases Nat.lt_or_ge x 24680310004633981344022529 with hc46 | hc46
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg193 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg194 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 24936064471014671286009857 with hc48 | hc48
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg195 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg196 x (by omega) (by omega)
