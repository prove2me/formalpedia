-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp052
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T22:44:51.169416+00:00
-- url     : https://prove2.me/submissions/ce319789-e6c1-435e-bff6-01dede474de1

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02551
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02552
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02553
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02554
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02555
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02556
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02557
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02558
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02559
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02560
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02561
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02562
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02563
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02564
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02565
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02566
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02567
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02568
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02569
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02570
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02571
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02572
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02573
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02574
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02575
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02576
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02577
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02578
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02579
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02580
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02581
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02582
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02583
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02584
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02585
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02586
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02587
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02588
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02589
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02590
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02591
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02592
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02593
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02594
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02595
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02596
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02597
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02598
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02599
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02600

theorem solution (n : Nat)
    (hn : 4989560667149 < n) (hupper : n <= 5645912403713) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 5307600442763 n with h2 | h2
  · -- n > 5307600442763
    rcases Nat.lt_or_ge 5467382526367 n with h4 | h4
    · -- n > 5467382526367
      rcases Nat.lt_or_ge 5549068421719 n with h6 | h6
      · -- n > 5549068421719
        rcases Nat.lt_or_ge 5590367899343 n with h8 | h8
        · -- n > 5590367899343
          rcases Nat.lt_or_ge 5618071507583 n with h10 | h10
          · -- n > 5618071507583
            rcases Nat.lt_or_ge 5631974752267 n with h12 | h12
            · -- n > 5631974752267
              exact RamareSaouter2003.prime_interval_nat_ladder_c02600 n (by omega) (by omega)
            · -- n <= 5631974752267
              exact RamareSaouter2003.prime_interval_nat_ladder_c02599 n (by omega) (by omega)
          · -- n <= 5618071507583
            rcases Nat.lt_or_ge 5604202584859 n with h12 | h12
            · -- n > 5604202584859
              exact RamareSaouter2003.prime_interval_nat_ladder_c02598 n (by omega) (by omega)
            · -- n <= 5604202584859
              exact RamareSaouter2003.prime_interval_nat_ladder_c02597 n (by omega) (by omega)
        · -- n <= 5590367899343
          rcases Nat.lt_or_ge 5562800901923 n with h10 | h10
          · -- n > 5562800901923
            rcases Nat.lt_or_ge 5576567366443 n with h12 | h12
            · -- n > 5576567366443
              exact RamareSaouter2003.prime_interval_nat_ladder_c02596 n (by omega) (by omega)
            · -- n <= 5576567366443
              exact RamareSaouter2003.prime_interval_nat_ladder_c02595 n (by omega) (by omega)
          · -- n <= 5562800901923
            exact RamareSaouter2003.prime_interval_nat_ladder_c02594 n (by omega) (by omega)
      · -- n <= 5549068421719
        rcases Nat.lt_or_ge 5508074048777 n with h8 | h8
        · -- n > 5508074048777
          rcases Nat.lt_or_ge 5521705078723 n with h10 | h10
          · -- n > 5521705078723
            rcases Nat.lt_or_ge 5535369841871 n with h12 | h12
            · -- n > 5535369841871
              exact RamareSaouter2003.prime_interval_nat_ladder_c02593 n (by omega) (by omega)
            · -- n <= 5535369841871
              exact RamareSaouter2003.prime_interval_nat_ladder_c02592 n (by omega) (by omega)
          · -- n <= 5521705078723
            exact RamareSaouter2003.prime_interval_nat_ladder_c02591 n (by omega) (by omega)
        · -- n <= 5508074048777
          rcases Nat.lt_or_ge 5480912855611 n with h10 | h10
          · -- n > 5480912855611
            rcases Nat.lt_or_ge 5494476668701 n with h12 | h12
            · -- n > 5494476668701
              exact RamareSaouter2003.prime_interval_nat_ladder_c02590 n (by omega) (by omega)
            · -- n <= 5494476668701
              exact RamareSaouter2003.prime_interval_nat_ladder_c02589 n (by omega) (by omega)
          · -- n <= 5480912855611
            exact RamareSaouter2003.prime_interval_nat_ladder_c02588 n (by omega) (by omega)
    · -- n <= 5467382526367
      rcases Nat.lt_or_ge 5386899100391 n with h6 | h6
      · -- n > 5386899100391
        rcases Nat.lt_or_ge 5426991617083 n with h8 | h8
        · -- n > 5426991617083
          rcases Nat.lt_or_ge 5440421989451 n with h10 | h10
          · -- n > 5440421989451
            rcases Nat.lt_or_ge 5453885598457 n with h12 | h12
            · -- n > 5453885598457
              exact RamareSaouter2003.prime_interval_nat_ladder_c02587 n (by omega) (by omega)
            · -- n <= 5453885598457
              exact RamareSaouter2003.prime_interval_nat_ladder_c02586 n (by omega) (by omega)
          · -- n <= 5440421989451
            exact RamareSaouter2003.prime_interval_nat_ladder_c02585 n (by omega) (by omega)
        · -- n <= 5426991617083
          rcases Nat.lt_or_ge 5400230254231 n with h10 | h10
          · -- n > 5400230254231
            rcases Nat.lt_or_ge 5413594399261 n with h12 | h12
            · -- n > 5413594399261
              exact RamareSaouter2003.prime_interval_nat_ladder_c02584 n (by omega) (by omega)
            · -- n <= 5413594399261
              exact RamareSaouter2003.prime_interval_nat_ladder_c02583 n (by omega) (by omega)
          · -- n <= 5400230254231
            exact RamareSaouter2003.prime_interval_nat_ladder_c02582 n (by omega) (by omega)
      · -- n <= 5386899100391
        rcases Nat.lt_or_ge 5347102771607 n with h8 | h8
        · -- n > 5347102771607
          rcases Nat.lt_or_ge 5360335440139 n with h10 | h10
          · -- n > 5360335440139
            rcases Nat.lt_or_ge 5373600856073 n with h12 | h12
            · -- n > 5373600856073
              exact RamareSaouter2003.prime_interval_nat_ladder_c02581 n (by omega) (by omega)
            · -- n <= 5373600856073
              exact RamareSaouter2003.prime_interval_nat_ladder_c02580 n (by omega) (by omega)
          · -- n <= 5360335440139
            exact RamareSaouter2003.prime_interval_nat_ladder_c02579 n (by omega) (by omega)
        · -- n <= 5347102771607
          rcases Nat.lt_or_ge 5320735353419 n with h10 | h10
          · -- n > 5320735353419
            rcases Nat.lt_or_ge 5333902769567 n with h12 | h12
            · -- n > 5333902769567
              exact RamareSaouter2003.prime_interval_nat_ladder_c02578 n (by omega) (by omega)
            · -- n <= 5333902769567
              exact RamareSaouter2003.prime_interval_nat_ladder_c02577 n (by omega) (by omega)
          · -- n <= 5320735353419
            exact RamareSaouter2003.prime_interval_nat_ladder_c02576 n (by omega) (by omega)
  · -- n <= 5307600442763
    rcases Nat.lt_or_ge 5139768356659 n with h4 | h4
    · -- n > 5139768356659
      rcases Nat.lt_or_ge 5216559504743 n with h6 | h6
      · -- n > 5216559504743
        rcases Nat.lt_or_ge 5255384252509 n with h8 | h8
        · -- n > 5255384252509
          rcases Nat.lt_or_ge 5281427816867 n with h10 | h10
          · -- n > 5281427816867
            rcases Nat.lt_or_ge 5294497957241 n with h12 | h12
            · -- n > 5294497957241
              exact RamareSaouter2003.prime_interval_nat_ladder_c02575 n (by omega) (by omega)
            · -- n <= 5294497957241
              exact RamareSaouter2003.prime_interval_nat_ladder_c02574 n (by omega) (by omega)
          · -- n <= 5281427816867
            rcases Nat.lt_or_ge 5268389941921 n with h12 | h12
            · -- n > 5268389941921
              exact RamareSaouter2003.prime_interval_nat_ladder_c02573 n (by omega) (by omega)
            · -- n <= 5268389941921
              exact RamareSaouter2003.prime_interval_nat_ladder_c02572 n (by omega) (by omega)
        · -- n <= 5255384252509
          rcases Nat.lt_or_ge 5229469113157 n with h10 | h10
          · -- n > 5229469113157
            rcases Nat.lt_or_ge 5242410669409 n with h12 | h12
            · -- n > 5242410669409
              exact RamareSaouter2003.prime_interval_nat_ladder_c02571 n (by omega) (by omega)
            · -- n <= 5242410669409
              exact RamareSaouter2003.prime_interval_nat_ladder_c02570 n (by omega) (by omega)
          · -- n <= 5229469113157
            exact RamareSaouter2003.prime_interval_nat_ladder_c02569 n (by omega) (by omega)
      · -- n <= 5216559504743
        rcases Nat.lt_or_ge 5178021578987 n with h8 | h8
        · -- n > 5178021578987
          rcases Nat.lt_or_ge 5190835816213 n with h10 | h10
          · -- n > 5190835816213
            rcases Nat.lt_or_ge 5203681765313 n with h12 | h12
            · -- n > 5203681765313
              exact RamareSaouter2003.prime_interval_nat_ladder_c02568 n (by omega) (by omega)
            · -- n <= 5203681765313
              exact RamareSaouter2003.prime_interval_nat_ladder_c02567 n (by omega) (by omega)
          · -- n <= 5190835816213
            exact RamareSaouter2003.prime_interval_nat_ladder_c02566 n (by omega) (by omega)
        · -- n <= 5178021578987
          rcases Nat.lt_or_ge 5152487927233 n with h10 | h10
          · -- n > 5152487927233
            rcases Nat.lt_or_ge 5165238975409 n with h12 | h12
            · -- n > 5165238975409
              exact RamareSaouter2003.prime_interval_nat_ladder_c02565 n (by omega) (by omega)
            · -- n <= 5165238975409
              exact RamareSaouter2003.prime_interval_nat_ladder_c02564 n (by omega) (by omega)
          · -- n <= 5152487927233
            exact RamareSaouter2003.prime_interval_nat_ladder_c02563 n (by omega) (by omega)
    · -- n <= 5139768356659
      rcases Nat.lt_or_ge 5064107624269 n with h6 | h6
      · -- n > 5064107624269
        rcases Nat.lt_or_ge 5101797734393 n with h8 | h8
        · -- n > 5101797734393
          rcases Nat.lt_or_ge 5114423337713 n with h10 | h10
          · -- n > 5114423337713
            rcases Nat.lt_or_ge 5127080186003 n with h12 | h12
            · -- n > 5127080186003
              exact RamareSaouter2003.prime_interval_nat_ladder_c02562 n (by omega) (by omega)
            · -- n <= 5127080186003
              exact RamareSaouter2003.prime_interval_nat_ladder_c02561 n (by omega) (by omega)
          · -- n <= 5114423337713
            exact RamareSaouter2003.prime_interval_nat_ladder_c02560 n (by omega) (by omega)
        · -- n <= 5101797734393
          rcases Nat.lt_or_ge 5076639954521 n with h10 | h10
          · -- n > 5076639954521
            rcases Nat.lt_or_ge 5089203298987 n with h12 | h12
            · -- n > 5089203298987
              exact RamareSaouter2003.prime_interval_nat_ladder_c02559 n (by omega) (by omega)
            · -- n <= 5089203298987
              exact RamareSaouter2003.prime_interval_nat_ladder_c02558 n (by omega) (by omega)
          · -- n <= 5076639954521
            exact RamareSaouter2003.prime_interval_nat_ladder_c02557 n (by omega) (by omega)
      · -- n <= 5064107624269
        rcases Nat.lt_or_ge 5026695954187 n with h8 | h8
        · -- n > 5026695954187
          rcases Nat.lt_or_ge 5039135700433 n with h10 | h10
          · -- n > 5039135700433
            rcases Nat.lt_or_ge 5051606231741 n with h12 | h12
            · -- n > 5051606231741
              exact RamareSaouter2003.prime_interval_nat_ladder_c02556 n (by omega) (by omega)
            · -- n <= 5051606231741
              exact RamareSaouter2003.prime_interval_nat_ladder_c02555 n (by omega) (by omega)
          · -- n <= 5039135700433
            exact RamareSaouter2003.prime_interval_nat_ladder_c02554 n (by omega) (by omega)
        · -- n <= 5026695954187
          rcases Nat.lt_or_ge 5001908513291 n with h10 | h10
          · -- n > 5001908513291
            rcases Nat.lt_or_ge 5014286917039 n with h12 | h12
            · -- n > 5014286917039
              exact RamareSaouter2003.prime_interval_nat_ladder_c02553 n (by omega) (by omega)
            · -- n <= 5014286917039
              exact RamareSaouter2003.prime_interval_nat_ladder_c02552 n (by omega) (by omega)
          · -- n <= 5001908513291
            exact RamareSaouter2003.prime_interval_nat_ladder_c02551 n (by omega) (by omega)
