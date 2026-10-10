-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_proth_grp10
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:00:30.366723+00:00
-- url     : https://prove2.me/submissions/45cdfd42-a2dd-41d0-a998-f25d42a58fd2

import Mathlib.Data.Nat.Prime.Defs
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg442
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg443
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg444
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg445
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg446
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg447
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg448
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg449
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg450
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg451
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg452
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg453
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg454
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg455
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg456
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg457
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg458
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg459
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg460
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg461
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg462
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg463
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg464
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg465
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg466
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg467
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg468
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg469
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg470
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg471
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg472
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg473
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg474
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg475
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg476
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg477
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg478
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg479
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg480
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg481
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg482
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg483
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg484
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg485
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg486
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg487
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg488
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg489
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_seg490

/-! Link reduction: `WeakGoldbach.prime_in_4e18_window_proth_grp10` (56393863834836779545919489 <= x < 62659848260934984706031617) from the 49 ladder segments `WeakGoldbach.prime_in_4e18_window_proth_seg442` .. `WeakGoldbach.prime_in_4e18_window_proth_seg490`, which tile that range end to end; a balanced case split on x selects the segment. -/

theorem solution (x : ℕ)
    (hxl : 56393863834836779545919489 ≤ x) (hx : x < 62659848260934984706031617) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  rcases Nat.lt_or_ge x 59462917430648594849857537 with hc24 | hc24
  · rcases Nat.lt_or_ge x 57928390633226472314109953 with hc12 | hc12
    · rcases Nat.lt_or_ge x 57161127233855704069570561 with hc6 | hc6
      · rcases Nat.lt_or_ge x 56777495534091155110100993 with hc3 | hc3
        · rcases Nat.lt_or_ge x 56521741067640096423936001 with hc1 | hc1
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg442 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 56649618301428575720439809 with hc2 | hc2
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg443 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg444 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 56905372767439829755494401 with hc4 | hc4
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg445 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 57033250000665359098576897 with hc5 | hc5
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg446 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg447 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 57544758933743398331351041 with hc9 | hc9
        · rcases Nat.lt_or_ge x 57289004467116417784741889 with hc7 | hc7
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg448 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 57416881699655851872092161 with hc8 | hc8
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg449 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg450 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 57672636166265240232656897 with hc10 | hc10
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg451 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 57800513399772244552450049 with hc11 | hc11
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg452 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg453 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 58695654032350949954027521 with hc18 | hc18
      · rcases Nat.lt_or_ge x 58312022331249394855182337 with hc15 | hc15
        · rcases Nat.lt_or_ge x 58056267866504778215325697 with hc13 | hc13
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg454 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 58184145099554385697964033 with hc14 | hc14
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg455 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg456 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 58439899565935075639951361 with hc16 | hc16
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg457 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 58567776798967090936545281 with hc17 | hc17
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg458 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg459 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 59079285731728470820519937 with hc21 | hc21
        · rcases Nat.lt_or_ge x 58823531264327434087956481 with hc19 | hc19
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg460 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 58951408498784416454148097 with hc20 | hc20
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg461 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg462 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 59207162965112329838002177 with hc22 | hc22
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg463 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 59335040197880462343929857 with hc23 | hc23
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg464 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg465 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 60997444229618829757513729 with hc36 | hc36
    · rcases Nat.lt_or_ge x 60230180830635089605951489 with hc30 | hc30
      · rcases Nat.lt_or_ge x 59846549131081646879014913 with hc27 | hc27
        · rcases Nat.lt_or_ge x 59590794664683364750983169 with hc25 | hc25
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg466 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 59718671897310759768555521 with hc26 | hc26
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg467 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg468 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 59974426363638673152409601 with hc28 | hc28
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg469 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 60102303595456827611938817 with hc29 | hc29
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg470 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg471 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 60613812530118163588710401 with hc33 | hc33
        · rcases Nat.lt_or_ge x 60358058063455998670012417 with hc31 | hc31
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg472 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 60485935296593567082872833 with hc32 | hc32
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg473 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg474 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 60741689763255732001570817 with hc34 | hc34
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg475 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 60869566996639591019053057 with hc35 | hc35
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg476 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg477 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 61764707627617407490588673 with hc42 | hc42
      · rcases Nat.lt_or_ge x 61381075929154680298405889 with hc39 | hc39
        · rcases Nat.lt_or_ge x 61125321462334185705308161 with hc37 | hc37
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg478 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 61253198696122665001811969 with hc38 | hc38
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg479 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg480 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 61508953162010773734555649 with hc40 | hc40
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg481 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 61636830395165934333460481 with hc41 | hc41
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg482 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg483 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 62148339328296750124367873 with hc45 | hc45
        · rcases Nat.lt_or_ge x 61892584861634585205669889 with hc43 | hc43
          · exact WeakGoldbach.prime_in_4e18_window_proth_seg484 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 62020462095053628595240961 with hc44 | hc44
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg485 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg486 x (by omega) (by omega)
        · rcases Nat.lt_or_ge x 62404093794888546298888193 with hc47 | hc47
          · rcases Nat.lt_or_ge x 62276216561117659188428801 with hc46 | hc46
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg487 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg488 x (by omega) (by omega)
          · rcases Nat.lt_or_ge x 62531971027392796014149633 with hc48 | hc48
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg489 x (by omega) (by omega)
            · exact WeakGoldbach.prime_in_4e18_window_proth_seg490 x (by omega) (by omega)
