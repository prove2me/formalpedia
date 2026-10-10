-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp08
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:55:44.185792+00:00
-- url     : https://prove2.me/submissions/4aed0f96-2e54-4433-a780-90e33c7ea078

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg344
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg345
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg346
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg347
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg348
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg349
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg350
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg351
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg352
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg353
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg354
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg355
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg356
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg357
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg358
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg359
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg360
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg361
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg362
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg363
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg364
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg365
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg366
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg367
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg368
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg369
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg370
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg371
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg372
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg373
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg374
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg375
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg376
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg377
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg378
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg379
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg380
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg381
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg382
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg383
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg384
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg385
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg386
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg387
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg388
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg389
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg390
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg391
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg392

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp08` (43861894982745922341961729 <= x < 50127879408826535316029441) from the 49 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg344` .. `WeakGoldbach.prime_in_4e18_window_proth_seg392`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 43861894982745922341961729 ≤ x) (hx : x < 50127879408826535316029441) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 46930948579261425087676417 with hc24 | hc24
  · rcases Nat.lt_or_ge x 45396421779657871482421249 with hc12 | hc12
    · rcases Nat.lt_or_ge x 44629158381641701563301889 with hc6 | hc6
      · rcases Nat.lt_or_ge x 44245526682316957254942721 with hc3 | hc3
        · rcases Nat.lt_or_ge x 43989772215672384522289153 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg344 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 44117649447279432749285377 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg345 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg346 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 44373403915454525667803137 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg347 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 44501281148222658173730817 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg348 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg349 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 45012790080104428755484673 with hc9 | hc9
        · rcases Nat.lt_or_ge x 44757035614286688766918657 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg350 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 44884912847230743133290497 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg351 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg352 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 45140667314279936144965633 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg353 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 45268544547593426418270209 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg354 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg355 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 46163685179767511540826113 with hc18 | hc18
      · rcases Nat.lt_or_ge x 45780053479703895418601473 with hc15 | hc15
        · rcases Nat.lt_or_ge x 45524299014132446034657281 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg356 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 45652176247375567563784193 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg357 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg358 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 45907930711750748296708097 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg359 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 46035807945873479128055809 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg360 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg361 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 46547316879268177709629441 with hc21 | hc21
        · rcases Nat.lt_or_ge x 46291562411585666000355329 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg362 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 46419439646253754599079937 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg363 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg364 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 46675194112792774215467009 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg365 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 46803071345648867651616769 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg366 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg367 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 48465475376032636739780609 with hc36 | hc36
    · rcases Nat.lt_or_ge x 47698211978192388681105409 with hc30 | hc30
      · rcases Nat.lt_or_ge x 47314580278832460000657409 with hc27 | hc27
        · rcases Nat.lt_or_ge x 47058825811343462337871873 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg368 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 47186703045219902564597761 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg369 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg370 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 47442457510492284785786881 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg371 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 47570334744861306221756417 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg372 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg373 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 48081843677605093919686657 with hc33 | hc33
        · rcases Nat.lt_or_ge x 47826089209693883791835137 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg374 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 47953966444731408297492481 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg375 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg376 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 48209720910971360751124481 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg377 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 48337598144144113536073729 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg378 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg379 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 49232738775966354937741313 with hc42 | hc42
      · rcases Nat.lt_or_ge x 48849107074636101420318721 with hc39 | hc39
        · rcases Nat.lt_or_ge x 48593352610472026919927809 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg380 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 48721229843416081286299649 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg381 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg382 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 48976984309480111879487489 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg383 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 49104861542934339641147393 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg384 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg385 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 49616370475748496083255297 with hc45 | hc45
        · rcases Nat.lt_or_ge x 49360616009719649862156289 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg386 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 49488493242980363577327617 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg387 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg388 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 49872124942533806304264193 with hc47 | hc47
          · rcases Nat.lt_or_ge x 49744247709149947286781953 with hc46 | hc46
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg389 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg390 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 50000002175002871647436801 with hc48 | hc48
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg391 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg392 x (by omega) (by omega)
