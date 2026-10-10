-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp09
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:58:06.023548+00:00
-- url     : https://prove2.me/submissions/0ad292a2-53bf-442c-b762-9c58a79ee806

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg393
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg394
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg395
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg396
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg397
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg398
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg399
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg400
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg401
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg402
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg403
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg404
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg405
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg406
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg407
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg408
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg409
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg410
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg411
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg412
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg413
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg414
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg415
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg416
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg417
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg418
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg419
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg420
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg421
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg422
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg423
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg424
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg425
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg426
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg427
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg428
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg429
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg430
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg431
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg432
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg433
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg434
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg435
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg436
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg437
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg438
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg439
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg440
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg441

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp09` (50127879408826535316029441 <= x < 56393863834836779545919489) from the 49 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg393` .. `WeakGoldbach.prime_in_4e18_window_proth_seg441`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 50127879408826535316029441 ≤ x) (hx : x < 56393863834836779545919489) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 53196933004972602154811393 with hc24 | hc24
  · rcases Nat.lt_or_ge x 51662406206846792177287169 with hc12 | hc12
    · rcases Nat.lt_or_ge x 50895142808021381700124673 with hc6 | hc6
      · rcases Nat.lt_or_ge x 50511511108186463996477441 with hc3 | hc3
        · rcases Nat.lt_or_ge x 50255756640679874147647489 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg393 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 50383633875084079955705857 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg394 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg395 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 50639388340532384037339137 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg396 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 50767265574567153938464769 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg397 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg398 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 51278774506167449543507969 with hc9 | hc9
        · rcases Nat.lt_or_ge x 51023020041053396996718593 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg399 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 51150897274226149781667841 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg400 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg401 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 51406651740149442886500353 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg402 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 51534528973797184694648833 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg403 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg404 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 52429669605513872980049921 with hc18 | hc18
      · rcases Nat.lt_or_ge x 52046037906470603648401409 with hc15 | hc15
        · rcases Nat.lt_or_ge x 51790283438612170078683137 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg405 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 51918160672998783700697089 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg406 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg407 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 52173915139924831410061313 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg408 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 52301792371830946799812609 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg409 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg410 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 52813301304803432916320257 with hc21 | hc21
        · rcases Nat.lt_or_ge x 52557546838739402323132417 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg411 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 52685424072510289433591809 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg412 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg413 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 52941178539049309049978881 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg414 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 53069055771764664997773313 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg415 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg416 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 54731459800969757620961281 with hc36 | hc36
    · rcases Nat.lt_or_ge x 53964196404413739143528449 with hc30 | hc30
      · rcases Nat.lt_or_ge x 53580564704913072974725121 with hc27 | hc27
        · rcases Nat.lt_or_ge x 53324810237793511218872321 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg417 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 53452687471705135817687041 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg418 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg419 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 53708441937522875806253057 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg420 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 53836319171328947288801281 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg421 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg422 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 54347828102243147638112257 with hc33 | hc33
        · rcases Nat.lt_or_ge x 54092073634437490626527233 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg423 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 54219950870548138480893953 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg424 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg425 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 54475705336770498748481537 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg426 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 54603582570048804649697281 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg427 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg428 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 55498723202715470981496833 with hc42 | hc42
      · rcases Nat.lt_or_ge x 55115091502810184533671937 with hc39 | hc39
        · rcases Nat.lt_or_ge x 54859337036587824266084353 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg429 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 54987214270042052027744257 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg430 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg431 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 55242968736211635737198593 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg432 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 55370845969560310382592001 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg433 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg434 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 55882354901600410638745601 with hc45 | hc45
        · rcases Nat.lt_or_ge x 55626600435835447208312833 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg435 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 55754477667284165760909313 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg436 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg437 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 56138109368069061510955009 with hc47 | hc47
          · rcases Nat.lt_or_ge x 56010232135529627423604737 with hc46 | hc46
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg438 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg439 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 56265986601699211133059073 with hc48 | hc48
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg440 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg441 x (by omega) (by omega)
