-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp034
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T10:18:16.78798+00:00
-- url     : https://prove2.me/submissions/7ca91ff7-b789-4cd3-85af-b0560c7fc46d

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01651
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01652
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01653
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01654
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01655
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01656
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01657
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01658
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01659
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01660
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01661
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01662
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01663
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01664
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01665
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01666
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01667
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01668
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01669
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01670
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01671
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01672
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01673
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01674
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01675
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01676
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01677
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01678
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01679
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01680
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01681
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01682
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01683
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01684
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01685
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01686
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01687
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01688
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01689
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01690
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01691
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01692
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01693
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01694
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01695
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01696
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01697
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01698
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01699
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01700

theorem solution (n : Nat)
    (hn : 516674572321 < n) (hupper : n <= 586248983429) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 550353355177 n with h2 | h2
  · -- n > 550353355177
    rcases Nat.lt_or_ge 567297747521 n with h4 | h4
    · -- n > 567297747521
      rcases Nat.lt_or_ge 575966412701 n with h6 | h6
      · -- n > 575966412701
        rcases Nat.lt_or_ge 580350753583 n with h8 | h8
        · -- n > 580350753583
          rcases Nat.lt_or_ge 583292344519 n with h10 | h10
          · -- n > 583292344519
            rcases Nat.lt_or_ge 584768778149 n with h12 | h12
            · -- n > 584768778149
              exact RamareSaouter2003.prime_interval_nat_ladder_c01700 n (by omega) (by omega)
            · -- n <= 584768778149
              exact RamareSaouter2003.prime_interval_nat_ladder_c01699 n (by omega) (by omega)
          · -- n <= 583292344519
            rcases Nat.lt_or_ge 581819672939 n with h12 | h12
            · -- n > 581819672939
              exact RamareSaouter2003.prime_interval_nat_ladder_c01698 n (by omega) (by omega)
            · -- n <= 581819672939
              exact RamareSaouter2003.prime_interval_nat_ladder_c01697 n (by omega) (by omega)
        · -- n <= 580350753583
          rcases Nat.lt_or_ge 577424133103 n with h10 | h10
          · -- n > 577424133103
            rcases Nat.lt_or_ge 578885576833 n with h12 | h12
            · -- n > 578885576833
              exact RamareSaouter2003.prime_interval_nat_ladder_c01696 n (by omega) (by omega)
            · -- n <= 578885576833
              exact RamareSaouter2003.prime_interval_nat_ladder_c01695 n (by omega) (by omega)
          · -- n <= 577424133103
            exact RamareSaouter2003.prime_interval_nat_ladder_c01694 n (by omega) (by omega)
      · -- n <= 575966412701
        rcases Nat.lt_or_ge 571615496369 n with h8 | h8
        · -- n > 571615496369
          rcases Nat.lt_or_ge 573062103899 n with h10 | h10
          · -- n > 573062103899
            rcases Nat.lt_or_ge 574512406163 n with h12 | h12
            · -- n > 574512406163
              exact RamareSaouter2003.prime_interval_nat_ladder_c01693 n (by omega) (by omega)
            · -- n <= 574512406163
              exact RamareSaouter2003.prime_interval_nat_ladder_c01692 n (by omega) (by omega)
          · -- n <= 573062103899
            exact RamareSaouter2003.prime_interval_nat_ladder_c01691 n (by omega) (by omega)
        · -- n <= 571615496369
          rcases Nat.lt_or_ge 568733327641 n with h10 | h10
          · -- n > 568733327641
            rcases Nat.lt_or_ge 570172574099 n with h12 | h12
            · -- n > 570172574099
              exact RamareSaouter2003.prime_interval_nat_ladder_c01690 n (by omega) (by omega)
            · -- n <= 570172574099
              exact RamareSaouter2003.prime_interval_nat_ladder_c01689 n (by omega) (by omega)
          · -- n <= 568733327641
            exact RamareSaouter2003.prime_interval_nat_ladder_c01688 n (by omega) (by omega)
    · -- n <= 567297747521
      rcases Nat.lt_or_ge 558760734089 n with h6 | h6
      · -- n > 558760734089
        rcases Nat.lt_or_ge 563012911229 n with h8 | h8
        · -- n > 563012911229
          rcases Nat.lt_or_ge 564437548607 n with h10 | h10
          · -- n > 564437548607
            rcases Nat.lt_or_ge 565865824291 n with h12 | h12
            · -- n > 565865824291
              exact RamareSaouter2003.prime_interval_nat_ladder_c01687 n (by omega) (by omega)
            · -- n <= 565865824291
              exact RamareSaouter2003.prime_interval_nat_ladder_c01686 n (by omega) (by omega)
          · -- n <= 564437548607
            exact RamareSaouter2003.prime_interval_nat_ladder_c01685 n (by omega) (by omega)
        · -- n <= 563012911229
          rcases Nat.lt_or_ge 560174513189 n with h10 | h10
          · -- n > 560174513189
            rcases Nat.lt_or_ge 561591902467 n with h12 | h12
            · -- n > 561591902467
              exact RamareSaouter2003.prime_interval_nat_ladder_c01684 n (by omega) (by omega)
            · -- n <= 561591902467
              exact RamareSaouter2003.prime_interval_nat_ladder_c01683 n (by omega) (by omega)
          · -- n <= 560174513189
            exact RamareSaouter2003.prime_interval_nat_ladder_c01682 n (by omega) (by omega)
      · -- n <= 558760734089
        rcases Nat.lt_or_ge 554540965169 n with h8 | h8
        · -- n > 554540965169
          rcases Nat.lt_or_ge 555943969313 n with h10 | h10
          · -- n > 555943969313
            rcases Nat.lt_or_ge 557350555907 n with h12 | h12
            · -- n > 557350555907
              exact RamareSaouter2003.prime_interval_nat_ladder_c01681 n (by omega) (by omega)
            · -- n <= 557350555907
              exact RamareSaouter2003.prime_interval_nat_ladder_c01680 n (by omega) (by omega)
          · -- n <= 555943969313
            exact RamareSaouter2003.prime_interval_nat_ladder_c01679 n (by omega) (by omega)
        · -- n <= 554540965169
          rcases Nat.lt_or_ge 551745667201 n with h10 | h10
          · -- n > 551745667201
            rcases Nat.lt_or_ge 553141534157 n with h12 | h12
            · -- n > 553141534157
              exact RamareSaouter2003.prime_interval_nat_ladder_c01678 n (by omega) (by omega)
            · -- n <= 553141534157
              exact RamareSaouter2003.prime_interval_nat_ladder_c01677 n (by omega) (by omega)
          · -- n <= 551745667201
            exact RamareSaouter2003.prime_interval_nat_ladder_c01676 n (by omega) (by omega)
  · -- n <= 550353355177
    rcases Nat.lt_or_ge 532572665441 n with h4 | h4
    · -- n > 532572665441
      rcases Nat.lt_or_ge 540705941981 n with h6 | h6
      · -- n > 540705941981
        rcases Nat.lt_or_ge 544819472849 n with h8 | h8
        · -- n > 544819472849
          rcases Nat.lt_or_ge 547579358941 n with h10 | h10
          · -- n > 547579358941
            rcases Nat.lt_or_ge 548964588763 n with h12 | h12
            · -- n > 548964588763
              exact RamareSaouter2003.prime_interval_nat_ladder_c01675 n (by omega) (by omega)
            · -- n <= 548964588763
              exact RamareSaouter2003.prime_interval_nat_ladder_c01674 n (by omega) (by omega)
          · -- n <= 547579358941
            rcases Nat.lt_or_ge 546197656651 n with h12 | h12
            · -- n > 546197656651
              exact RamareSaouter2003.prime_interval_nat_ladder_c01673 n (by omega) (by omega)
            · -- n <= 546197656651
              exact RamareSaouter2003.prime_interval_nat_ladder_c01672 n (by omega) (by omega)
        · -- n <= 544819472849
          rcases Nat.lt_or_ge 542073624553 n with h10 | h10
          · -- n > 542073624553
            rcases Nat.lt_or_ge 543444798529 n with h12 | h12
            · -- n > 543444798529
              exact RamareSaouter2003.prime_interval_nat_ladder_c01671 n (by omega) (by omega)
            · -- n <= 543444798529
              exact RamareSaouter2003.prime_interval_nat_ladder_c01670 n (by omega) (by omega)
          · -- n <= 542073624553
            exact RamareSaouter2003.prime_interval_nat_ladder_c01669 n (by omega) (by omega)
      · -- n <= 540705941981
        rcases Nat.lt_or_ge 536623753117 n with h8 | h8
        · -- n > 536623753117
          rcases Nat.lt_or_ge 537981015211 n with h10 | h10
          · -- n > 537981015211
            rcases Nat.lt_or_ge 539341741843 n with h12 | h12
            · -- n > 539341741843
              exact RamareSaouter2003.prime_interval_nat_ladder_c01668 n (by omega) (by omega)
            · -- n <= 539341741843
              exact RamareSaouter2003.prime_interval_nat_ladder_c01667 n (by omega) (by omega)
          · -- n <= 537981015211
            exact RamareSaouter2003.prime_interval_nat_ladder_c01666 n (by omega) (by omega)
        · -- n <= 536623753117
          rcases Nat.lt_or_ge 533919587153 n with h10 | h10
          · -- n > 533919587153
            rcases Nat.lt_or_ge 535269946811 n with h12 | h12
            · -- n > 535269946811
              exact RamareSaouter2003.prime_interval_nat_ladder_c01665 n (by omega) (by omega)
            · -- n <= 535269946811
              exact RamareSaouter2003.prime_interval_nat_ladder_c01664 n (by omega) (by omega)
          · -- n <= 533919587153
            exact RamareSaouter2003.prime_interval_nat_ladder_c01663 n (by omega) (by omega)
    · -- n <= 532572665441
      rcases Nat.lt_or_ge 524562839041 n with h6 | h6
      · -- n > 524562839041
        rcases Nat.lt_or_ge 528552439763 n with h8 | h8
        · -- n > 528552439763
          rcases Nat.lt_or_ge 529889100553 n with h10 | h10
          · -- n > 529889100553
            rcases Nat.lt_or_ge 531229172863 n with h12 | h12
            · -- n > 531229172863
              exact RamareSaouter2003.prime_interval_nat_ladder_c01662 n (by omega) (by omega)
            · -- n <= 531229172863
              exact RamareSaouter2003.prime_interval_nat_ladder_c01661 n (by omega) (by omega)
          · -- n <= 529889100553
            exact RamareSaouter2003.prime_interval_nat_ladder_c01660 n (by omega) (by omega)
        · -- n <= 528552439763
          rcases Nat.lt_or_ge 525889317799 n with h10 | h10
          · -- n > 525889317799
            rcases Nat.lt_or_ge 527219181673 n with h12 | h12
            · -- n > 527219181673
              exact RamareSaouter2003.prime_interval_nat_ladder_c01659 n (by omega) (by omega)
            · -- n <= 527219181673
              exact RamareSaouter2003.prime_interval_nat_ladder_c01658 n (by omega) (by omega)
          · -- n <= 525889317799
            exact RamareSaouter2003.prime_interval_nat_ladder_c01657 n (by omega) (by omega)
      · -- n <= 524562839041
        rcases Nat.lt_or_ge 520603627667 n with h8 | h8
        · -- n > 520603627667
          rcases Nat.lt_or_ge 521920002647 n with h10 | h10
          · -- n > 521920002647
            rcases Nat.lt_or_ge 523239736939 n with h12 | h12
            · -- n > 523239736939
              exact RamareSaouter2003.prime_interval_nat_ladder_c01656 n (by omega) (by omega)
            · -- n <= 523239736939
              exact RamareSaouter2003.prime_interval_nat_ladder_c01655 n (by omega) (by omega)
          · -- n <= 521920002647
            exact RamareSaouter2003.prime_interval_nat_ladder_c01654 n (by omega) (by omega)
        · -- n <= 520603627667
          rcases Nat.lt_or_ge 517980921169 n with h10 | h10
          · -- n > 517980921169
            rcases Nat.lt_or_ge 519290603323 n with h12 | h12
            · -- n > 519290603323
              exact RamareSaouter2003.prime_interval_nat_ladder_c01653 n (by omega) (by omega)
            · -- n <= 519290603323
              exact RamareSaouter2003.prime_interval_nat_ladder_c01652 n (by omega) (by omega)
          · -- n <= 517980921169
            exact RamareSaouter2003.prime_interval_nat_ladder_c01651 n (by omega) (by omega)
