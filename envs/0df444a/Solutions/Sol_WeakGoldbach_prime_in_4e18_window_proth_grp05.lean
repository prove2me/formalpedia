-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp05
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:45:15.380984+00:00
-- url     : https://prove2.me/submissions/934649e5-cc7f-4d65-85b6-95bcc4f38f32

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg197
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg198
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg199
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg200
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg201
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg202
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg203
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg204
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg205
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg206
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg207
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg208
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg209
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg210
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg211
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg212
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg213
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg214
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg215
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg216
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg217
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg218
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg219
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg220
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg221
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg222
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg223
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg224
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg225
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg226
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg227
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg228
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg229
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg230
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg231
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg232
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg233
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg234
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg235
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg236
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg237
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg238
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg239
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg240
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg241
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg242
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg243
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg244
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg245

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp05` (25063941703624474117537793 <= x < 31329926130109707370627073) from the 49 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg197` .. `WeakGoldbach.prime_in_4e18_window_proth_seg245`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 25063941703624474117537793 ≤ x) (hx : x < 31329926130109707370627073) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 28132995299964055002808321 with hc24 | hc24
  · rcases Nat.lt_or_ge x 26598468502260457490350081 with hc12 | hc12
    · rcases Nat.lt_or_ge x 25831205102854504873721857 with hc6 | hc6
      · rcases Nat.lt_or_ge x 25447573403758458983940097 with hc3 | hc3
        · rcases Nat.lt_or_ge x 25191818937184254995464193 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg197 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 25319696170532929640857601 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg198 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg199 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 25575450636368261815468033 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg200 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 25703327869400277112061953 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg201 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg202 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 26214836802847752251768833 with hc9 | hc9
        · rcases Nat.lt_or_ge x 25959082336414285751648257 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg203 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 26086959569604630722641921 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg204 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg205 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 26342714036108465966940161 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg206 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 26470591268929375031001089 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg207 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg208 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 27365731901525672618622977 with hc18 | hc18
      · rcases Nat.lt_or_ge x 26982100202060190821908481 with hc15 | hc15
        · rcases Nat.lt_or_ge x 26726345734993405624188929 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg209 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 26854222968289303711449089 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg210 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg211 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 27109977433614462490771457 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg212 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 27237854667913115182563329 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg213 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg214 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 27749363600621718508404737 with hc21 | hc21
        · rcases Nat.lt_or_ge x 27493609134276212938506241 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg215 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 27621486365936037723635713 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg216 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg217 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 27877240833864840037531649 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg218 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 28005118065102452357595137 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg219 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg220 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 29667522098951882096508929 with hc36 | hc36
    · rcases Nat.lt_or_ge x 28900258699844996642635777 with hc30 | hc30
      · rcases Nat.lt_or_ge x 28516627000344330473832449 with hc27 | hc27
        · rcases Nat.lt_or_ge x 28260872533699757741178881 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg221 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 28388749767101208944705537 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg222 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg223 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 28644504232936541119315969 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg224 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 28772381465775042369421313 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg225 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg226 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 29283890399275294067261441 with hc33 | hc33
        · rcases Nat.lt_or_ge x 29028135932718682264829953 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg227 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 29156013165926619421868033 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg228 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg229 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 29411767630987895410524161 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg230 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 29539644865796721497604097 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg231 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg232 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 30434785497759700387627009 with hc42 | hc42
      · rcases Nat.lt_or_ge x 30051153798452548265312257 with hc39 | hc39
        · rcases Nat.lt_or_ge x 29795399332036673951236097 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg233 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 29923276565314979852451841 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg234 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg235 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 30179031031695669794439169 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg236 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 30306908264938791323566081 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg237 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg238 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 30818417197330735300608001 with hc45 | hc45
        · rcases Nat.lt_or_ge x 30562662730967637544665089 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg239 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 30690539964263535631925249 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg240 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg241 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 31074171663658648684462081 with hc47 | hc47
          · rcases Nat.lt_or_ge x 30946294430415527155335169 with hc46 | hc46
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg242 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg243 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 31202048896901770213588993 with hc48 | hc48
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg244 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg245 x (by omega) (by omega)
