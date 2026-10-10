-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:02:38.693034+00:00
-- url     : https://prove2.me/submissions/fce8c3e6-53ea-4de8-bd58-9f619c79b332

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg491
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg492
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg493
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg494
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg495
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg496
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg497
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg498
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg499
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg500
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg501
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg502
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg503
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg504
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg505
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg506
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg507
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg508
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg509
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg510
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg511
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg512
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg513
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg514
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg515
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg516
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg517
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg518
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg519
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg520
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg521
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg522
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg523
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg524
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg525
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg526
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg527
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg528
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg529
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg530
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg531
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg532
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg533
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg534
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg535
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg536
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg537
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg538
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg539

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp11` (62659848260934984706031617 <= x < 68925832687279480470765569) from the 49 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg491` .. `WeakGoldbach.prime_in_4e18_window_proth_seg539`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 62659848260934984706031617 ≤ x) (hx : x < 68925832687279480470765569) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 65728901856764392196014081 with hc24 | hc24
  · rcases Nat.lt_or_ge x 64194375058550621288267777 with hc12 | hc12
    · rcases Nat.lt_or_ge x 63427111660252976392437761 with hc6 | hc6
      · rcases Nat.lt_or_ge x 63043479960312505572524033 with hc3 | hc3
        · rcases Nat.lt_or_ge x 62787725493967000002625537 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg491 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 62915602727157344973619201 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg492 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg493 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 63171357192165844404142081 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg494 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 63299234426112653375045633 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg495 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg496 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 63810743358926809817153537 with hc9 | hc9
        · rcases Nat.lt_or_ge x 63554988893372952619253761 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg497 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 63682866126053124194959361 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg498 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg499 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 63938620592943987532234753 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg500 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 64066497826081555945095169 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg501 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg502 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 64961638458572300416450561 with hc18 | hc18
      · rcases Nat.lt_or_ge x 64578006758948488945336321 with hc15 | hc15
        · rcases Nat.lt_or_ge x 64322252292145586538283009 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg503 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 64450129525124825276743681 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg504 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg505 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 64705883992191610474463233 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg506 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 64833761225223625771057153 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg507 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg508 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 65345270158108150957342721 with hc21 | hc21
        · rcases Nat.lt_or_ge x 65089515691340432922378241 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg509 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 65217392924390040405016577 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg510 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg511 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 65473147390805914719092737 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg512 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 65601024624172181550530561 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg513 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg514 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 67263428654696688127049729 with hc36 | hc36
    · rcases Nat.lt_or_ge x 66496165256135160440553473 with hc30 | hc30
      · rcases Nat.lt_or_ge x 66112533556141913062506497 with hc27 | hc27
        · rcases Nat.lt_or_ge x 65856779090904715213406209 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg515 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 65984656324112652370444289 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg516 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg517 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 66240410790440565754298369 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg518 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 66368288023419804492759041 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg519 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg520 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 66879796956181184376733697 with hc33 | hc33
        · rcases Nat.lt_or_ge x 66624042489782902248701953 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg521 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 66751919722726956615073793 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg522 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg523 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 67007674189301160603549697 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg524 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 67135551422720203993120769 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg525 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg526 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 68030692052660081488035841 with hc42 | hc42
      · rcases Nat.lt_or_ge x 67647060354584382388830209 with hc39 | hc39
        · rcases Nat.lt_or_ge x 67391305887095384726044673 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg527 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 67519183121587551464325121 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg528 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg529 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 67774937588284900755111937 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg530 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 67902814820525267679707137 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg531 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg532 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 68414323753832005331058689 with hc45 | hc45
        · rcases Nat.lt_or_ge x 68158569288084634086670337 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg533 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 68286446521362939987886081 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg534 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg535 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 68670078220476578063712257 with hc47 | hc47
          · rcases Nat.lt_or_ge x 68542200987532523697340417 with hc46 | hc46
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg536 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg537 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 68797955453930805825372161 with hc48 | hc48
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg538 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg539 x (by omega) (by omega)
