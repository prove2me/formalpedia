-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp033
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T09:46:54.933461+00:00
-- url     : https://prove2.me/submissions/087c9042-6076-41c7-ad1e-562cdc5679d3

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01601
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01602
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01603
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01604
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01605
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01606
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01607
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01608
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01609
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01610
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01611
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01612
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01613
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01614
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01615
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01616
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01617
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01618
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01619
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01620
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01621
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01622
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01623
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01624
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01625
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01626
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01627
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01628
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01629
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01630
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01631
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01632
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01633
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01634
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01635
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01636
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01637
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01638
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01639
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01640
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01641
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01642
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01643
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01644
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01645
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01646
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01647
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01648
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01649
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01650

theorem solution (n : Nat)
    (hn : 455423937959 < n) (hupper : n <= 516674572321) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 485074565777 n with h2 | h2
  · -- n > 485074565777
    rcases Nat.lt_or_ge 499991515981 n with h4 | h4
    · -- n > 499991515981
      rcases Nat.lt_or_ge 507622750567 n with h6 | h6
      · -- n > 507622750567
        rcases Nat.lt_or_ge 511482340337 n with h8 | h8
        · -- n > 511482340337
          rcases Nat.lt_or_ge 514071840677 n with h10 | h10
          · -- n > 514071840677
            rcases Nat.lt_or_ge 515371548353 n with h12 | h12
            · -- n > 515371548353
              exact RamareSaouter2003.prime_interval_nat_ladder_c01650 n (by omega) (by omega)
            · -- n <= 515371548353
              exact RamareSaouter2003.prime_interval_nat_ladder_c01649 n (by omega) (by omega)
          · -- n <= 514071840677
            rcases Nat.lt_or_ge 512775440839 n with h12 | h12
            · -- n > 512775440839
              exact RamareSaouter2003.prime_interval_nat_ladder_c01648 n (by omega) (by omega)
            · -- n <= 512775440839
              exact RamareSaouter2003.prime_interval_nat_ladder_c01647 n (by omega) (by omega)
        · -- n <= 511482340337
          rcases Nat.lt_or_ge 508906003601 n with h10 | h10
          · -- n > 508906003601
            rcases Nat.lt_or_ge 510192530699 n with h12 | h12
            · -- n > 510192530699
              exact RamareSaouter2003.prime_interval_nat_ladder_c01646 n (by omega) (by omega)
            · -- n <= 510192530699
              exact RamareSaouter2003.prime_interval_nat_ladder_c01645 n (by omega) (by omega)
          · -- n <= 508906003601
            exact RamareSaouter2003.prime_interval_nat_ladder_c01644 n (by omega) (by omega)
      · -- n <= 507622750567
        rcases Nat.lt_or_ge 503792550973 n with h8 | h8
        · -- n > 503792550973
          rcases Nat.lt_or_ge 505066032587 n with h10 | h10
          · -- n > 505066032587
            rcases Nat.lt_or_ge 506342762911 n with h12 | h12
            · -- n > 506342762911
              exact RamareSaouter2003.prime_interval_nat_ladder_c01643 n (by omega) (by omega)
            · -- n <= 506342762911
              exact RamareSaouter2003.prime_interval_nat_ladder_c01642 n (by omega) (by omega)
          · -- n <= 505066032587
            exact RamareSaouter2003.prime_interval_nat_ladder_c01641 n (by omega) (by omega)
        · -- n <= 503792550973
          rcases Nat.lt_or_ge 501255301081 n with h10 | h10
          · -- n > 501255301081
            rcases Nat.lt_or_ge 502522309937 n with h12 | h12
            · -- n > 502522309937
              exact RamareSaouter2003.prime_interval_nat_ladder_c01640 n (by omega) (by omega)
            · -- n <= 502522309937
              exact RamareSaouter2003.prime_interval_nat_ladder_c01639 n (by omega) (by omega)
          · -- n <= 501255301081
            exact RamareSaouter2003.prime_interval_nat_ladder_c01638 n (by omega) (by omega)
    · -- n <= 499991515981
      rcases Nat.lt_or_ge 492476044937 n with h6 | h6
      · -- n > 492476044937
        rcases Nat.lt_or_ge 496219421447 n with h8 | h8
        · -- n > 496219421447
          rcases Nat.lt_or_ge 497473584383 n with h10 | h10
          · -- n > 497473584383
            rcases Nat.lt_or_ge 498730946509 n with h12 | h12
            · -- n > 498730946509
              exact RamareSaouter2003.prime_interval_nat_ladder_c01637 n (by omega) (by omega)
            · -- n <= 498730946509
              exact RamareSaouter2003.prime_interval_nat_ladder_c01636 n (by omega) (by omega)
          · -- n <= 497473584383
            exact RamareSaouter2003.prime_interval_nat_ladder_c01635 n (by omega) (by omega)
        · -- n <= 496219421447
          rcases Nat.lt_or_ge 493720659863 n with h10 | h10
          · -- n > 493720659863
            rcases Nat.lt_or_ge 494968449307 n with h12 | h12
            · -- n > 494968449307
              exact RamareSaouter2003.prime_interval_nat_ladder_c01634 n (by omega) (by omega)
            · -- n <= 494968449307
              exact RamareSaouter2003.prime_interval_nat_ladder_c01633 n (by omega) (by omega)
          · -- n <= 493720659863
            exact RamareSaouter2003.prime_interval_nat_ladder_c01632 n (by omega) (by omega)
      · -- n <= 492476044937
        rcases Nat.lt_or_ge 488761165931 n with h8 | h8
        · -- n > 488761165931
          rcases Nat.lt_or_ge 489996306067 n with h10 | h10
          · -- n > 489996306067
            rcases Nat.lt_or_ge 491234596373 n with h12 | h12
            · -- n > 491234596373
              exact RamareSaouter2003.prime_interval_nat_ladder_c01631 n (by omega) (by omega)
            · -- n <= 491234596373
              exact RamareSaouter2003.prime_interval_nat_ladder_c01630 n (by omega) (by omega)
          · -- n <= 489996306067
            exact RamareSaouter2003.prime_interval_nat_ladder_c01629 n (by omega) (by omega)
        · -- n <= 488761165931
          rcases Nat.lt_or_ge 486300303851 n with h10 | h10
          · -- n > 486300303851
            rcases Nat.lt_or_ge 487529167949 n with h12 | h12
            · -- n > 487529167949
              exact RamareSaouter2003.prime_interval_nat_ladder_c01628 n (by omega) (by omega)
            · -- n <= 487529167949
              exact RamareSaouter2003.prime_interval_nat_ladder_c01627 n (by omega) (by omega)
          · -- n <= 486300303851
            exact RamareSaouter2003.prime_interval_nat_ladder_c01626 n (by omega) (by omega)
  · -- n <= 485074565777
    rcases Nat.lt_or_ge 469420809181 n with h4 | h4
    · -- n > 469420809181
      rcases Nat.lt_or_ge 476581254251 n with h6 | h6
      · -- n > 476581254251
        rcases Nat.lt_or_ge 480202712659 n with h8 | h8
        · -- n > 480202712659
          rcases Nat.lt_or_ge 482632435393 n with h10 | h10
          · -- n > 482632435393
            rcases Nat.lt_or_ge 483851945581 n with h12 | h12
            · -- n > 483851945581
              exact RamareSaouter2003.prime_interval_nat_ladder_c01625 n (by omega) (by omega)
            · -- n <= 483851945581
              exact RamareSaouter2003.prime_interval_nat_ladder_c01624 n (by omega) (by omega)
          · -- n <= 482632435393
            rcases Nat.lt_or_ge 481416027031 n with h12 | h12
            · -- n > 481416027031
              exact RamareSaouter2003.prime_interval_nat_ladder_c01623 n (by omega) (by omega)
            · -- n <= 481416027031
              exact RamareSaouter2003.prime_interval_nat_ladder_c01622 n (by omega) (by omega)
        · -- n <= 480202712659
          rcases Nat.lt_or_ge 477785334239 n with h10 | h10
          · -- n > 477785334239
            rcases Nat.lt_or_ge 478992484423 n with h12 | h12
            · -- n > 478992484423
              exact RamareSaouter2003.prime_interval_nat_ladder_c01621 n (by omega) (by omega)
            · -- n <= 478992484423
              exact RamareSaouter2003.prime_interval_nat_ladder_c01620 n (by omega) (by omega)
          · -- n <= 477785334239
            exact RamareSaouter2003.prime_interval_nat_ladder_c01619 n (by omega) (by omega)
      · -- n <= 476581254251
        rcases Nat.lt_or_ge 472987356979 n with h8 | h8
        · -- n > 472987356979
          rcases Nat.lt_or_ge 474182273429 n with h10 | h10
          · -- n > 474182273429
            rcases Nat.lt_or_ge 475380236621 n with h12 | h12
            · -- n > 475380236621
              exact RamareSaouter2003.prime_interval_nat_ladder_c01618 n (by omega) (by omega)
            · -- n <= 475380236621
              exact RamareSaouter2003.prime_interval_nat_ladder_c01617 n (by omega) (by omega)
          · -- n <= 474182273429
            exact RamareSaouter2003.prime_interval_nat_ladder_c01616 n (by omega) (by omega)
        · -- n <= 472987356979
          rcases Nat.lt_or_ge 470606632579 n with h10 | h10
          · -- n > 470606632579
            rcases Nat.lt_or_ge 471795479263 n with h12 | h12
            · -- n > 471795479263
              exact RamareSaouter2003.prime_interval_nat_ladder_c01615 n (by omega) (by omega)
            · -- n <= 471795479263
              exact RamareSaouter2003.prime_interval_nat_ladder_c01614 n (by omega) (by omega)
          · -- n <= 470606632579
            exact RamareSaouter2003.prime_interval_nat_ladder_c01613 n (by omega) (by omega)
    · -- n <= 469420809181
      rcases Nat.lt_or_ge 462368923909 n with h6 | h6
      · -- n > 462368923909
        rcases Nat.lt_or_ge 465881400979 n with h8 | h8
        · -- n > 465881400979
          rcases Nat.lt_or_ge 467058201041 n with h10 | h10
          · -- n > 467058201041
            rcases Nat.lt_or_ge 468238001237 n with h12 | h12
            · -- n > 468238001237
              exact RamareSaouter2003.prime_interval_nat_ladder_c01612 n (by omega) (by omega)
            · -- n <= 468238001237
              exact RamareSaouter2003.prime_interval_nat_ladder_c01611 n (by omega) (by omega)
          · -- n <= 467058201041
            exact RamareSaouter2003.prime_interval_nat_ladder_c01610 n (by omega) (by omega)
        · -- n <= 465881400979
          rcases Nat.lt_or_ge 463536770083 n with h10 | h10
          · -- n > 463536770083
            rcases Nat.lt_or_ge 464707593169 n with h12 | h12
            · -- n > 464707593169
              exact RamareSaouter2003.prime_interval_nat_ladder_c01609 n (by omega) (by omega)
            · -- n <= 464707593169
              exact RamareSaouter2003.prime_interval_nat_ladder_c01608 n (by omega) (by omega)
          · -- n <= 463536770083
            exact RamareSaouter2003.prime_interval_nat_ladder_c01607 n (by omega) (by omega)
      · -- n <= 462368923909
        rcases Nat.lt_or_ge 458883171287 n with h8 | h8
        · -- n > 458883171287
          rcases Nat.lt_or_ge 460042132133 n with h10 | h10
          · -- n > 460042132133
            rcases Nat.lt_or_ge 461204047151 n with h12 | h12
            · -- n > 461204047151
              exact RamareSaouter2003.prime_interval_nat_ladder_c01606 n (by omega) (by omega)
            · -- n <= 461204047151
              exact RamareSaouter2003.prime_interval_nat_ladder_c01605 n (by omega) (by omega)
          · -- n <= 460042132133
            exact RamareSaouter2003.prime_interval_nat_ladder_c01604 n (by omega) (by omega)
        · -- n <= 458883171287
          rcases Nat.lt_or_ge 456574081753 n with h10 | h10
          · -- n > 456574081753
            rcases Nat.lt_or_ge 457727157077 n with h12 | h12
            · -- n > 457727157077
              exact RamareSaouter2003.prime_interval_nat_ladder_c01603 n (by omega) (by omega)
            · -- n <= 457727157077
              exact RamareSaouter2003.prime_interval_nat_ladder_c01602 n (by omega) (by omega)
          · -- n <= 456574081753
            exact RamareSaouter2003.prime_interval_nat_ladder_c01601 n (by omega) (by omega)
