-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp07
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:53:01.081983+00:00
-- url     : https://prove2.me/submissions/0ac2061d-d51c-441f-a04b-31ea47291d7f

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg295
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg296
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg297
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg298
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg299
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg300
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg301
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg302
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg303
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg304
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg305
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg306
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg307
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg308
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg309
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg310
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg311
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg312
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg313
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg314
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg315
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg316
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg317
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg318
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg319
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg320
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg321
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg322
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg323
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg324
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg325
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg326
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg327
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg328
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg329
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg330
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg331
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg332
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg333
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg334
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg335
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg336
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg337
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg338
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg339
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg340
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg341
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg342
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg343

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp07` (37595910556489387507449857 <= x < 43861894982745922341961729) from the 49 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg295` .. `WeakGoldbach.prime_in_4e18_window_proth_seg343`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 37595910556489387507449857 ≤ x) (hx : x < 43861894982745922341961729) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 40664964152793784020631553 with hc24 | hc24
  · rcases Nat.lt_or_ge x 39130437354755934973329409 with hc12 | hc12
    · rcases Nat.lt_or_ge x 38363173955402758914834433 with hc6 | hc6
      · rcases Nat.lt_or_ge x 37979542256060422420430849 with hc3 | hc3
        · rcases Nat.lt_or_ge x 37723787789626955920310273 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg295 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 37851665022799708705259521 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg296 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg297 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 38107419488969292414713857 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg298 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 38235296721156882781175809 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg299 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg300 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 38746805654815464153415681 with hc9 | hc9
        · rcases Nat.lt_or_ge x 38491051187959785188229121 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg301 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 38618928419953861508202497 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg302 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg303 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 38874682888480798147608577 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg304 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 39002560121424852513980417 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg305 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg306 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 39897700752420261171560449 with hc18 | hc18
      · rcases Nat.lt_or_ge x 39514069054291785514221569 with hc15 | hc15
        · rcases Nat.lt_or_ge x 39258314587471290921123841 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg307 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 39386191821136624915316737 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg308 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg309 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 39641946287482130485215233 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg310 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 39769823520232670805098497 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg311 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg312 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 40281332453099603805339649 with hc21 | hc21
        · rcases Nat.lt_or_ge x 40025577986771690421485569 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg313 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 40153455219926851020390401 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg314 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg315 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 40409209686307540962377729 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg316 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 40537086919392332817104897 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg317 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg318 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 42199490950866817440022529 with hc36 | hc36
    · rcases Nat.lt_or_ge x 41432227552146960079126529 with hc30 | hc30
      · rcases Nat.lt_or_ge x 41048595852417595491745793 with hc27 | hc27
        · rcases Nat.lt_or_ge x 40792841385403586852159489 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg319 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 40920718619315211450974209 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg320 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg321 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 41176473085027398323273729 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg322 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 41304350317742754271068161 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg323 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg324 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 41815859251278190340997121 with hc33 | hc33
        · rcases Nat.lt_or_ge x 41560104785178975375720449 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg325 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 41687982018263767230447617 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg326 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg327 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 41943736484679641544523777 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg328 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 42071613718098684934094849 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg329 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg330 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 42966754350360730986872833 with hc42 | hc42
      · rcases Nat.lt_or_ge x 42583122650912841376202753 with hc39 | hc39
        · rcases Nat.lt_or_ge x 42327368184197899899371521 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg331 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 42455245416614188684410881 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg332 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg333 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 42710999884103186347196417 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg334 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 42838877116853726667079681 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg335 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg336 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 43350386049720659667320833 with hc45 | hc45
        · rcases Nat.lt_or_ge x 43094631583551075957866497 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg337 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 43222508816706236556771329 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg338 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg339 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 43606140515151371562909697 with hc47 | hc47
          · rcases Nat.lt_or_ge x 43478263283069334312714241 with hc46 | hc46
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg340 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg341 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 43734017747251000999149569 with hc48 | hc48
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg342 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg343 x (by omega) (by omega)
