-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp035
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T10:51:54.76902+00:00
-- url     : https://prove2.me/submissions/ed501020-3ad6-4d5d-86b2-51f4b47f9a78

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01701
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01702
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01703
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01704
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01705
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01706
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01707
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01708
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01709
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01710
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01711
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01712
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01713
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01714
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01715
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01716
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01717
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01718
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01719
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01720
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01721
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01722
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01723
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01724
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01725
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01726
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01727
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01728
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01729
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01730
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01731
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01732
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01733
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01734
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01735
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01736
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01737
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01738
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01739
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01740
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01741
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01742
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01743
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01744
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01745
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01746
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01747
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01748
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01749
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01750

theorem solution (n : Nat)
    (hn : 586248983429 < n) (hupper : n <= 665289962371) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 624508782791 n with h2 | h2
  · -- n > 624508782791
    rcases Nat.lt_or_ge 643759006883 n with h4 | h4
    · -- n > 643759006883
      rcases Nat.lt_or_ge 653607583709 n with h6 | h6
      · -- n > 653607583709
        rcases Nat.lt_or_ge 658588753201 n with h8 | h8
        · -- n > 658588753201
          rcases Nat.lt_or_ge 661930799767 n with h10 | h10
          · -- n > 661930799767
            rcases Nat.lt_or_ge 663608236063 n with h12 | h12
            · -- n > 663608236063
              exact RamareSaouter2003.prime_interval_nat_ladder_c01750 n (by omega) (by omega)
            · -- n <= 663608236063
              exact RamareSaouter2003.prime_interval_nat_ladder_c01749 n (by omega) (by omega)
          · -- n <= 661930799767
            rcases Nat.lt_or_ge 660257642479 n with h12 | h12
            · -- n > 660257642479
              exact RamareSaouter2003.prime_interval_nat_ladder_c01748 n (by omega) (by omega)
            · -- n <= 660257642479
              exact RamareSaouter2003.prime_interval_nat_ladder_c01747 n (by omega) (by omega)
        · -- n <= 658588753201
          rcases Nat.lt_or_ge 655263734759 n with h10 | h10
          · -- n > 655263734759
            rcases Nat.lt_or_ge 656924120959 n with h12 | h12
            · -- n > 656924120959
              exact RamareSaouter2003.prime_interval_nat_ladder_c01746 n (by omega) (by omega)
            · -- n <= 656924120959
              exact RamareSaouter2003.prime_interval_nat_ladder_c01745 n (by omega) (by omega)
          · -- n <= 655263734759
            exact RamareSaouter2003.prime_interval_nat_ladder_c01744 n (by omega) (by omega)
      · -- n <= 653607583709
        rcases Nat.lt_or_ge 648664432607 n with h8 | h8
        · -- n > 648664432607
          rcases Nat.lt_or_ge 650307943567 n with h10 | h10
          · -- n > 650307943567
            rcases Nat.lt_or_ge 651955656907 n with h12 | h12
            · -- n > 651955656907
              exact RamareSaouter2003.prime_interval_nat_ladder_c01743 n (by omega) (by omega)
            · -- n <= 651955656907
              exact RamareSaouter2003.prime_interval_nat_ladder_c01742 n (by omega) (by omega)
          · -- n <= 650307943567
            exact RamareSaouter2003.prime_interval_nat_ladder_c01741 n (by omega) (by omega)
        · -- n <= 648664432607
          rcases Nat.lt_or_ge 645389974997 n with h10 | h10
          · -- n > 645389974997
            rcases Nat.lt_or_ge 647025113347 n with h12 | h12
            · -- n > 647025113347
              exact RamareSaouter2003.prime_interval_nat_ladder_c01740 n (by omega) (by omega)
            · -- n <= 647025113347
              exact RamareSaouter2003.prime_interval_nat_ladder_c01739 n (by omega) (by omega)
          · -- n <= 645389974997
            exact RamareSaouter2003.prime_interval_nat_ladder_c01738 n (by omega) (by omega)
    · -- n <= 643759006883
      rcases Nat.lt_or_ge 634060172173 n with h6 | h6
      · -- n > 634060172173
        rcases Nat.lt_or_ge 638891016167 n with h8 | h8
        · -- n > 638891016167
          rcases Nat.lt_or_ge 640509538129 n with h10 | h10
          · -- n > 640509538129
            rcases Nat.lt_or_ge 642132198137 n with h12 | h12
            · -- n > 642132198137
              exact RamareSaouter2003.prime_interval_nat_ladder_c01737 n (by omega) (by omega)
            · -- n <= 642132198137
              exact RamareSaouter2003.prime_interval_nat_ladder_c01736 n (by omega) (by omega)
          · -- n <= 640509538129
            exact RamareSaouter2003.prime_interval_nat_ladder_c01735 n (by omega) (by omega)
        · -- n <= 638891016167
          rcases Nat.lt_or_ge 635666343791 n with h10 | h10
          · -- n > 635666343791
            rcases Nat.lt_or_ge 637276621559 n with h12 | h12
            · -- n > 637276621559
              exact RamareSaouter2003.prime_interval_nat_ladder_c01734 n (by omega) (by omega)
            · -- n <= 637276621559
              exact RamareSaouter2003.prime_interval_nat_ladder_c01733 n (by omega) (by omega)
          · -- n <= 635666343791
            exact RamareSaouter2003.prime_interval_nat_ladder_c01732 n (by omega) (by omega)
      · -- n <= 634060172173
        rcases Nat.lt_or_ge 629266189037 n with h8 | h8
        · -- n > 629266189037
          rcases Nat.lt_or_ge 630860105327 n with h10 | h10
          · -- n > 630860105327
            rcases Nat.lt_or_ge 632458096219 n with h12 | h12
            · -- n > 632458096219
              exact RamareSaouter2003.prime_interval_nat_ladder_c01731 n (by omega) (by omega)
            · -- n <= 632458096219
              exact RamareSaouter2003.prime_interval_nat_ladder_c01730 n (by omega) (by omega)
          · -- n <= 630860105327
            exact RamareSaouter2003.prime_interval_nat_ladder_c01729 n (by omega) (by omega)
        · -- n <= 629266189037
          rcases Nat.lt_or_ge 626090538209 n with h10 | h10
          · -- n > 626090538209
            rcases Nat.lt_or_ge 627676336849 n with h12 | h12
            · -- n > 627676336849
              exact RamareSaouter2003.prime_interval_nat_ladder_c01728 n (by omega) (by omega)
            · -- n <= 627676336849
              exact RamareSaouter2003.prime_interval_nat_ladder_c01727 n (by omega) (by omega)
          · -- n <= 626090538209
            exact RamareSaouter2003.prime_interval_nat_ladder_c01726 n (by omega) (by omega)
  · -- n <= 624508782791
    rcases Nat.lt_or_ge 604309198267 n with h4 | h4
    · -- n > 604309198267
      rcases Nat.lt_or_ge 613548834383 n with h6 | h6
      · -- n > 613548834383
        rcases Nat.lt_or_ge 618221985613 n with h8 | h8
        · -- n > 618221985613
          rcases Nat.lt_or_ge 621357360073 n with h10 | h10
          · -- n > 621357360073
            rcases Nat.lt_or_ge 622931060233 n with h12 | h12
            · -- n > 622931060233
              exact RamareSaouter2003.prime_interval_nat_ladder_c01725 n (by omega) (by omega)
            · -- n <= 622931060233
              exact RamareSaouter2003.prime_interval_nat_ladder_c01724 n (by omega) (by omega)
          · -- n <= 621357360073
            rcases Nat.lt_or_ge 619787671973 n with h12 | h12
            · -- n > 619787671973
              exact RamareSaouter2003.prime_interval_nat_ladder_c01723 n (by omega) (by omega)
            · -- n <= 619787671973
              exact RamareSaouter2003.prime_interval_nat_ladder_c01722 n (by omega) (by omega)
        · -- n <= 618221985613
          rcases Nat.lt_or_ge 615102577069 n with h10 | h10
          · -- n > 615102577069
            rcases Nat.lt_or_ge 616660290737 n with h12 | h12
            · -- n > 616660290737
              exact RamareSaouter2003.prime_interval_nat_ladder_c01721 n (by omega) (by omega)
            · -- n <= 616660290737
              exact RamareSaouter2003.prime_interval_nat_ladder_c01720 n (by omega) (by omega)
          · -- n <= 615102577069
            exact RamareSaouter2003.prime_interval_nat_ladder_c01719 n (by omega) (by omega)
      · -- n <= 613548834383
        rcases Nat.lt_or_ge 608911330189 n with h8 | h8
        · -- n > 608911330189
          rcases Nat.lt_or_ge 610453221151 n with h10 | h10
          · -- n > 610453221151
            rcases Nat.lt_or_ge 611999052409 n with h12 | h12
            · -- n > 611999052409
              exact RamareSaouter2003.prime_interval_nat_ladder_c01718 n (by omega) (by omega)
            · -- n <= 611999052409
              exact RamareSaouter2003.prime_interval_nat_ladder_c01717 n (by omega) (by omega)
          · -- n <= 610453221151
            exact RamareSaouter2003.prime_interval_nat_ladder_c01716 n (by omega) (by omega)
        · -- n <= 608911330189
          rcases Nat.lt_or_ge 605839328813 n with h10 | h10
          · -- n > 605839328813
            rcases Nat.lt_or_ge 607373369419 n with h12 | h12
            · -- n > 607373369419
              exact RamareSaouter2003.prime_interval_nat_ladder_c01715 n (by omega) (by omega)
            · -- n <= 607373369419
              exact RamareSaouter2003.prime_interval_nat_ladder_c01714 n (by omega) (by omega)
          · -- n <= 605839328813
            exact RamareSaouter2003.prime_interval_nat_ladder_c01713 n (by omega) (by omega)
    · -- n <= 604309198267
      rcases Nat.lt_or_ge 595209965573 n with h6 | h6
      · -- n > 595209965573
        rcases Nat.lt_or_ge 599742166729 n with h8 | h8
        · -- n > 599742166729
          rcases Nat.lt_or_ge 601260627259 n with h10 | h10
          · -- n > 601260627259
            rcases Nat.lt_or_ge 602782967741 n with h12 | h12
            · -- n > 602782967741
              exact RamareSaouter2003.prime_interval_nat_ladder_c01712 n (by omega) (by omega)
            · -- n <= 602782967741
              exact RamareSaouter2003.prime_interval_nat_ladder_c01711 n (by omega) (by omega)
          · -- n <= 601260627259
            exact RamareSaouter2003.prime_interval_nat_ladder_c01710 n (by omega) (by omega)
        · -- n <= 599742166729
          rcases Nat.lt_or_ge 596716845773 n with h10 | h10
          · -- n > 596716845773
            rcases Nat.lt_or_ge 598227576229 n with h12 | h12
            · -- n > 598227576229
              exact RamareSaouter2003.prime_interval_nat_ladder_c01709 n (by omega) (by omega)
            · -- n <= 598227576229
              exact RamareSaouter2003.prime_interval_nat_ladder_c01708 n (by omega) (by omega)
          · -- n <= 596716845773
            exact RamareSaouter2003.prime_interval_nat_ladder_c01707 n (by omega) (by omega)
      · -- n <= 595209965573
        rcases Nat.lt_or_ge 590712326389 n with h8 | h8
        · -- n > 590712326389
          rcases Nat.lt_or_ge 592207715683 n with h10 | h10
          · -- n > 592207715683
            rcases Nat.lt_or_ge 593706925489 n with h12 | h12
            · -- n > 593706925489
              exact RamareSaouter2003.prime_interval_nat_ladder_c01706 n (by omega) (by omega)
            · -- n <= 593706925489
              exact RamareSaouter2003.prime_interval_nat_ladder_c01705 n (by omega) (by omega)
          · -- n <= 592207715683
            exact RamareSaouter2003.prime_interval_nat_ladder_c01704 n (by omega) (by omega)
        · -- n <= 590712326389
          rcases Nat.lt_or_ge 587732970059 n with h10 | h10
          · -- n > 587732970059
            rcases Nat.lt_or_ge 589220747777 n with h12 | h12
            · -- n > 589220747777
              exact RamareSaouter2003.prime_interval_nat_ladder_c01703 n (by omega) (by omega)
            · -- n <= 589220747777
              exact RamareSaouter2003.prime_interval_nat_ladder_c01702 n (by omega) (by omega)
          · -- n <= 587732970059
            exact RamareSaouter2003.prime_interval_nat_ladder_c01701 n (by omega) (by omega)
