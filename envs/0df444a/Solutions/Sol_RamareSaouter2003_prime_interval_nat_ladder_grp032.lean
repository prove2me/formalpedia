-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp032
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T09:15:00.744775+00:00
-- url     : https://prove2.me/submissions/c0a2314e-080d-4635-8e95-0265a7470a5d

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01551
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01552
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01553
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01554
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01555
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01556
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01557
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01558
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01559
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01560
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01561
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01562
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01563
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01564
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01565
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01566
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01567
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01568
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01569
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01570
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01571
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01572
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01573
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01574
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01575
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01576
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01577
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01578
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01579
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01580
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01581
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01582
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01583
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01584
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01585
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01586
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01587
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01588
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01589
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01590
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01591
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01592
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01593
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01594
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01595
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01596
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01597
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01598
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01599
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01600

theorem solution (n : Nat)
    (hn : 401493320309 < n) (hupper : n <= 455423937959) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 427601412241 n with h2 | h2
  · -- n > 427601412241
    rcases Nat.lt_or_ge 440735436829 n with h4 | h4
    · -- n > 440735436829
      rcases Nat.lt_or_ge 447454383097 n with h6 | h6
      · -- n > 447454383097
        rcases Nat.lt_or_ge 450852527207 n with h8 | h8
        · -- n > 450852527207
          rcases Nat.lt_or_ge 453132414619 n with h10 | h10
          · -- n > 453132414619
            rcases Nat.lt_or_ge 454276718057 n with h12 | h12
            · -- n > 454276718057
              exact RamareSaouter2003.prime_interval_nat_ladder_c01600 n (by omega) (by omega)
            · -- n <= 454276718057
              exact RamareSaouter2003.prime_interval_nat_ladder_c01599 n (by omega) (by omega)
          · -- n <= 453132414619
            rcases Nat.lt_or_ge 451991020157 n with h12 | h12
            · -- n > 451991020157
              exact RamareSaouter2003.prime_interval_nat_ladder_c01598 n (by omega) (by omega)
            · -- n <= 451991020157
              exact RamareSaouter2003.prime_interval_nat_ladder_c01597 n (by omega) (by omega)
        · -- n <= 450852527207
          rcases Nat.lt_or_ge 448584216109 n with h10 | h10
          · -- n > 448584216109
            rcases Nat.lt_or_ge 449716928333 n with h12 | h12
            · -- n > 449716928333
              exact RamareSaouter2003.prime_interval_nat_ladder_c01596 n (by omega) (by omega)
            · -- n <= 449716928333
              exact RamareSaouter2003.prime_interval_nat_ladder_c01595 n (by omega) (by omega)
          · -- n <= 448584216109
            exact RamareSaouter2003.prime_interval_nat_ladder_c01594 n (by omega) (by omega)
      · -- n <= 447454383097
        rcases Nat.lt_or_ge 444082085743 n with h8 | h8
        · -- n > 444082085743
          rcases Nat.lt_or_ge 445203325289 n with h10 | h10
          · -- n > 445203325289
            rcases Nat.lt_or_ge 446327421949 n with h12 | h12
            · -- n > 446327421949
              exact RamareSaouter2003.prime_interval_nat_ladder_c01593 n (by omega) (by omega)
            · -- n <= 446327421949
              exact RamareSaouter2003.prime_interval_nat_ladder_c01592 n (by omega) (by omega)
          · -- n <= 445203325289
            exact RamareSaouter2003.prime_interval_nat_ladder_c01591 n (by omega) (by omega)
        · -- n <= 444082085743
          rcases Nat.lt_or_ge 441848148823 n with h10 | h10
          · -- n > 441848148823
            rcases Nat.lt_or_ge 442963696027 n with h12 | h12
            · -- n > 442963696027
              exact RamareSaouter2003.prime_interval_nat_ladder_c01590 n (by omega) (by omega)
            · -- n <= 442963696027
              exact RamareSaouter2003.prime_interval_nat_ladder_c01589 n (by omega) (by omega)
          · -- n <= 441848148823
            exact RamareSaouter2003.prime_interval_nat_ladder_c01588 n (by omega) (by omega)
    · -- n <= 440735436829
      rcases Nat.lt_or_ge 434118298729 n with h6 | h6
      · -- n > 434118298729
        rcases Nat.lt_or_ge 437414239621 n with h8 | h8
        · -- n > 437414239621
          rcases Nat.lt_or_ge 438518489483 n with h10 | h10
          · -- n > 438518489483
            rcases Nat.lt_or_ge 439625552783 n with h12 | h12
            · -- n > 439625552783
              exact RamareSaouter2003.prime_interval_nat_ladder_c01587 n (by omega) (by omega)
            · -- n <= 439625552783
              exact RamareSaouter2003.prime_interval_nat_ladder_c01586 n (by omega) (by omega)
          · -- n <= 438518489483
            exact RamareSaouter2003.prime_interval_nat_ladder_c01585 n (by omega) (by omega)
        · -- n <= 437414239621
          rcases Nat.lt_or_ge 435214151483 n with h10 | h10
          · -- n > 435214151483
            rcases Nat.lt_or_ge 436312796021 n with h12 | h12
            · -- n > 436312796021
              exact RamareSaouter2003.prime_interval_nat_ladder_c01584 n (by omega) (by omega)
            · -- n <= 436312796021
              exact RamareSaouter2003.prime_interval_nat_ladder_c01583 n (by omega) (by omega)
          · -- n <= 435214151483
            exact RamareSaouter2003.prime_interval_nat_ladder_c01582 n (by omega) (by omega)
      · -- n <= 434118298729
        rcases Nat.lt_or_ge 430847420389 n with h8 | h8
        · -- n > 430847420389
          rcases Nat.lt_or_ge 431934940279 n with h10 | h10
          · -- n > 431934940279
            rcases Nat.lt_or_ge 433025230747 n with h12 | h12
            · -- n > 433025230747
              exact RamareSaouter2003.prime_interval_nat_ladder_c01581 n (by omega) (by omega)
            · -- n <= 433025230747
              exact RamareSaouter2003.prime_interval_nat_ladder_c01580 n (by omega) (by omega)
          · -- n <= 431934940279
            exact RamareSaouter2003.prime_interval_nat_ladder_c01579 n (by omega) (by omega)
        · -- n <= 430847420389
          rcases Nat.lt_or_ge 428680663457 n with h10 | h10
          · -- n > 428680663457
            rcases Nat.lt_or_ge 429762663727 n with h12 | h12
            · -- n > 429762663727
              exact RamareSaouter2003.prime_interval_nat_ladder_c01578 n (by omega) (by omega)
            · -- n <= 429762663727
              exact RamareSaouter2003.prime_interval_nat_ladder_c01577 n (by omega) (by omega)
          · -- n <= 428680663457
            exact RamareSaouter2003.prime_interval_nat_ladder_c01576 n (by omega) (by omega)
  · -- n <= 427601412241
    rcases Nat.lt_or_ge 413818141169 n with h4 | h4
    · -- n > 413818141169
      rcases Nat.lt_or_ge 420123041539 n with h6 | h6
      · -- n > 420123041539
        rcases Nat.lt_or_ge 423311758757 n with h8 | h8
        · -- n > 423311758757
          rcases Nat.lt_or_ge 425451129247 n with h10 | h10
          · -- n > 425451129247
            rcases Nat.lt_or_ge 426524903201 n with h12 | h12
            · -- n > 426524903201
              exact RamareSaouter2003.prime_interval_nat_ladder_c01575 n (by omega) (by omega)
            · -- n <= 426524903201
              exact RamareSaouter2003.prime_interval_nat_ladder_c01574 n (by omega) (by omega)
          · -- n <= 425451129247
            rcases Nat.lt_or_ge 424380083447 n with h12 | h12
            · -- n > 424380083447
              exact RamareSaouter2003.prime_interval_nat_ladder_c01573 n (by omega) (by omega)
            · -- n <= 424380083447
              exact RamareSaouter2003.prime_interval_nat_ladder_c01572 n (by omega) (by omega)
        · -- n <= 423311758757
          rcases Nat.lt_or_ge 421183244719 n with h10 | h10
          · -- n > 421183244719
            rcases Nat.lt_or_ge 422246148151 n with h12 | h12
            · -- n > 422246148151
              exact RamareSaouter2003.prime_interval_nat_ladder_c01571 n (by omega) (by omega)
            · -- n <= 422246148151
              exact RamareSaouter2003.prime_interval_nat_ladder_c01570 n (by omega) (by omega)
          · -- n <= 421183244719
            exact RamareSaouter2003.prime_interval_nat_ladder_c01569 n (by omega) (by omega)
      · -- n <= 420123041539
        rcases Nat.lt_or_ge 416958564331 n with h8 | h8
        · -- n > 416958564331
          rcases Nat.lt_or_ge 418010708249 n with h10 | h10
          · -- n > 418010708249
            rcases Nat.lt_or_ge 419065531699 n with h12 | h12
            · -- n > 419065531699
              exact RamareSaouter2003.prime_interval_nat_ladder_c01568 n (by omega) (by omega)
            · -- n <= 419065531699
              exact RamareSaouter2003.prime_interval_nat_ladder_c01567 n (by omega) (by omega)
          · -- n <= 418010708249
            exact RamareSaouter2003.prime_interval_nat_ladder_c01566 n (by omega) (by omega)
        · -- n <= 416958564331
          rcases Nat.lt_or_ge 414862287647 n with h10 | h10
          · -- n > 414862287647
            rcases Nat.lt_or_ge 415909093109 n with h12 | h12
            · -- n > 415909093109
              exact RamareSaouter2003.prime_interval_nat_ladder_c01565 n (by omega) (by omega)
            · -- n <= 415909093109
              exact RamareSaouter2003.prime_interval_nat_ladder_c01564 n (by omega) (by omega)
          · -- n <= 414862287647
            exact RamareSaouter2003.prime_interval_nat_ladder_c01563 n (by omega) (by omega)
    · -- n <= 413818141169
      rcases Nat.lt_or_ge 407608720423 n with h6 | h6
      · -- n > 407608720423
        rcases Nat.lt_or_ge 410701587509 n with h8 | h8
        · -- n > 410701587509
          rcases Nat.lt_or_ge 411737797879 n with h10 | h10
          · -- n > 411737797879
            rcases Nat.lt_or_ge 412776646837 n with h12 | h12
            · -- n > 412776646837
              exact RamareSaouter2003.prime_interval_nat_ladder_c01562 n (by omega) (by omega)
            · -- n <= 412776646837
              exact RamareSaouter2003.prime_interval_nat_ladder_c01561 n (by omega) (by omega)
          · -- n <= 411737797879
            exact RamareSaouter2003.prime_interval_nat_ladder_c01560 n (by omega) (by omega)
        · -- n <= 410701587509
          rcases Nat.lt_or_ge 408637055509 n with h10 | h10
          · -- n > 408637055509
            rcases Nat.lt_or_ge 409668008963 n with h12 | h12
            · -- n > 409668008963
              exact RamareSaouter2003.prime_interval_nat_ladder_c01559 n (by omega) (by omega)
            · -- n <= 409668008963
              exact RamareSaouter2003.prime_interval_nat_ladder_c01558 n (by omega) (by omega)
          · -- n <= 408637055509
            exact RamareSaouter2003.prime_interval_nat_ladder_c01557 n (by omega) (by omega)
      · -- n <= 407608720423
        rcases Nat.lt_or_ge 404539358017 n with h8 | h8
        · -- n > 404539358017
          rcases Nat.lt_or_ge 405559878323 n with h10 | h10
          · -- n > 405559878323
            rcases Nat.lt_or_ge 406582996903 n with h12 | h12
            · -- n > 406582996903
              exact RamareSaouter2003.prime_interval_nat_ladder_c01556 n (by omega) (by omega)
            · -- n <= 406582996903
              exact RamareSaouter2003.prime_interval_nat_ladder_c01555 n (by omega) (by omega)
          · -- n <= 405559878323
            exact RamareSaouter2003.prime_interval_nat_ladder_c01554 n (by omega) (by omega)
        · -- n <= 404539358017
          rcases Nat.lt_or_ge 402506085689 n with h10 | h10
          · -- n > 402506085689
            rcases Nat.lt_or_ge 403521429361 n with h12 | h12
            · -- n > 403521429361
              exact RamareSaouter2003.prime_interval_nat_ladder_c01553 n (by omega) (by omega)
            · -- n <= 403521429361
              exact RamareSaouter2003.prime_interval_nat_ladder_c01552 n (by omega) (by omega)
          · -- n <= 402506085689
            exact RamareSaouter2003.prime_interval_nat_ladder_c01551 n (by omega) (by omega)
