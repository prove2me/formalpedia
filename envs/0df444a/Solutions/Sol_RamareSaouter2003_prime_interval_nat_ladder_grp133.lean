-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp133
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T00:28:57.496449+00:00
-- url     : https://prove2.me/submissions/ba5e065e-d4c9-4b15-a13b-ddb8384ad939

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06601
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06602
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06603
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06604
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06605
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06606
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06607
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06608
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06609
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06610
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06611
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06612
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06613
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06614
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06615
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06616
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06617
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06618
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06619
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06620
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06621
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06622
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06623
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06624
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06625
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06626
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06627
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06628
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06629
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06630
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06631
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06632
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06633
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06634
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06635
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06636
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06637
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06638
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06639
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06640
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06641
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06642
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06643
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06644
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06645
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06646
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06647
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06648
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06649
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06650

theorem solution (n : Nat)
    (hn : 286750217619026779 < n) (hupper : n <= 330290864187526579) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 307751548060408073 n with h2 | h2
  · -- n > 307751548060408073
    rcases Nat.lt_or_ge 318371712477729571 n with h4 | h4
    · -- n > 318371712477729571
      rcases Nat.lt_or_ge 323818492502192819 n with h6 | h6
      · -- n > 323818492502192819
        rcases Nat.lt_or_ge 326576723231288077 n with h8 | h8
        · -- n > 326576723231288077
          rcases Nat.lt_or_ge 328428568474548397 n with h10 | h10
          · -- n > 328428568474548397
            rcases Nat.lt_or_ge 329358404556018727 n with h12 | h12
            · -- n > 329358404556018727
              exact RamareSaouter2003.prime_interval_nat_ladder_c06650 n (by omega) (by omega)
            · -- n <= 329358404556018727
              exact RamareSaouter2003.prime_interval_nat_ladder_c06649 n (by omega) (by omega)
          · -- n <= 328428568474548397
            rcases Nat.lt_or_ge 327501360750431767 n with h12 | h12
            · -- n > 327501360750431767
              exact RamareSaouter2003.prime_interval_nat_ladder_c06648 n (by omega) (by omega)
            · -- n <= 327501360750431767
              exact RamareSaouter2003.prime_interval_nat_ladder_c06647 n (by omega) (by omega)
        · -- n <= 326576723231288077
          rcases Nat.lt_or_ge 324735301498578251 n with h10 | h10
          · -- n > 324735301498578251
            rcases Nat.lt_or_ge 325654727013605831 n with h12 | h12
            · -- n > 325654727013605831
              exact RamareSaouter2003.prime_interval_nat_ladder_c06646 n (by omega) (by omega)
            · -- n <= 325654727013605831
              exact RamareSaouter2003.prime_interval_nat_ladder_c06645 n (by omega) (by omega)
          · -- n <= 324735301498578251
            exact RamareSaouter2003.prime_interval_nat_ladder_c06644 n (by omega) (by omega)
      · -- n <= 323818492502192819
        rcases Nat.lt_or_ge 321083550228544637 n with h8 | h8
        · -- n > 321083550228544637
          rcases Nat.lt_or_ge 321992623492162849 n with h10 | h10
          · -- n > 321992623492162849
            rcases Nat.lt_or_ge 322904262653063167 n with h12 | h12
            · -- n > 322904262653063167
              exact RamareSaouter2003.prime_interval_nat_ladder_c06643 n (by omega) (by omega)
            · -- n <= 322904262653063167
              exact RamareSaouter2003.prime_interval_nat_ladder_c06642 n (by omega) (by omega)
          · -- n <= 321992623492162849
            exact RamareSaouter2003.prime_interval_nat_ladder_c06641 n (by omega) (by omega)
        · -- n <= 321083550228544637
          rcases Nat.lt_or_ge 319273116003372649 n with h10 | h10
          · -- n > 319273116003372649
            rcases Nat.lt_or_ge 320177062391041333 n with h12 | h12
            · -- n > 320177062391041333
              exact RamareSaouter2003.prime_interval_nat_ladder_c06640 n (by omega) (by omega)
            · -- n <= 320177062391041333
              exact RamareSaouter2003.prime_interval_nat_ladder_c06639 n (by omega) (by omega)
          · -- n <= 319273116003372649
            exact RamareSaouter2003.prime_interval_nat_ladder_c06638 n (by omega) (by omega)
    · -- n <= 318371712477729571
      rcases Nat.lt_or_ge 313016602192835977 n with h6 | h6
      · -- n > 313016602192835977
        rcases Nat.lt_or_ge 315682842703633547 n with h8 | h8
        · -- n > 315682842703633547
          rcases Nat.lt_or_ge 316576637570507311 n with h10 | h10
          · -- n > 316576637570507311
            rcases Nat.lt_or_ge 317472853179778609 n with h12 | h12
            · -- n > 317472853179778609
              exact RamareSaouter2003.prime_interval_nat_ladder_c06637 n (by omega) (by omega)
            · -- n <= 317472853179778609
              exact RamareSaouter2003.prime_interval_nat_ladder_c06636 n (by omega) (by omega)
          · -- n <= 316576637570507311
            exact RamareSaouter2003.prime_interval_nat_ladder_c06635 n (by omega) (by omega)
        · -- n <= 315682842703633547
          rcases Nat.lt_or_ge 313902835363469591 n with h10 | h10
          · -- n > 313902835363469591
            rcases Nat.lt_or_ge 314791578227261969 n with h12 | h12
            · -- n > 314791578227261969
              exact RamareSaouter2003.prime_interval_nat_ladder_c06634 n (by omega) (by omega)
            · -- n <= 314791578227261969
              exact RamareSaouter2003.prime_interval_nat_ladder_c06633 n (by omega) (by omega)
          · -- n <= 313902835363469591
            exact RamareSaouter2003.prime_interval_nat_ladder_c06632 n (by omega) (by omega)
      · -- n <= 313016602192835977
        rcases Nat.lt_or_ge 310372910221627427 n with h8 | h8
        · -- n > 310372910221627427
          rcases Nat.lt_or_ge 311251636513599853 n with h10 | h10
          · -- n > 311251636513599853
            rcases Nat.lt_or_ge 312132858702292213 n with h12 | h12
            · -- n > 312132858702292213
              exact RamareSaouter2003.prime_interval_nat_ladder_c06631 n (by omega) (by omega)
            · -- n <= 312132858702292213
              exact RamareSaouter2003.prime_interval_nat_ladder_c06630 n (by omega) (by omega)
          · -- n <= 311251636513599853
            exact RamareSaouter2003.prime_interval_nat_ladder_c06629 n (by omega) (by omega)
        · -- n <= 310372910221627427
          rcases Nat.lt_or_ge 308622887338201019 n with h10 | h10
          · -- n > 308622887338201019
            rcases Nat.lt_or_ge 309496671153389219 n with h12 | h12
            · -- n > 309496671153389219
              exact RamareSaouter2003.prime_interval_nat_ladder_c06628 n (by omega) (by omega)
            · -- n <= 309496671153389219
              exact RamareSaouter2003.prime_interval_nat_ladder_c06627 n (by omega) (by omega)
          · -- n <= 308622887338201019
            exact RamareSaouter2003.prime_interval_nat_ladder_c06626 n (by omega) (by omega)
  · -- n <= 307751548060408073
    rcases Nat.lt_or_ge 296645691562227547 n with h4 | h4
    · -- n > 296645691562227547
      rcases Nat.lt_or_ge 301720814559769511 n with h6 | h6
      · -- n > 301720814559769511
        rcases Nat.lt_or_ge 304290778938698477 n with h8 | h8
        · -- n > 304290778938698477
          rcases Nat.lt_or_ge 306016260089416021 n with h10 | h10
          · -- n > 306016260089416021
            rcases Nat.lt_or_ge 306882669282213931 n with h12 | h12
            · -- n > 306882669282213931
              exact RamareSaouter2003.prime_interval_nat_ladder_c06625 n (by omega) (by omega)
            · -- n <= 306882669282213931
              exact RamareSaouter2003.prime_interval_nat_ladder_c06624 n (by omega) (by omega)
          · -- n <= 306016260089416021
            rcases Nat.lt_or_ge 305152307604695069 n with h12 | h12
            · -- n > 305152307604695069
              exact RamareSaouter2003.prime_interval_nat_ladder_c06623 n (by omega) (by omega)
            · -- n <= 305152307604695069
              exact RamareSaouter2003.prime_interval_nat_ladder_c06622 n (by omega) (by omega)
        · -- n <= 304290778938698477
          rcases Nat.lt_or_ge 302575076145073229 n with h10 | h10
          · -- n > 302575076145073229
            rcases Nat.lt_or_ge 303431710850136047 n with h12 | h12
            · -- n > 303431710850136047
              exact RamareSaouter2003.prime_interval_nat_ladder_c06621 n (by omega) (by omega)
            · -- n <= 303431710850136047
              exact RamareSaouter2003.prime_interval_nat_ladder_c06620 n (by omega) (by omega)
          · -- n <= 302575076145073229
            exact RamareSaouter2003.prime_interval_nat_ladder_c06619 n (by omega) (by omega)
      · -- n <= 301720814559769511
        rcases Nat.lt_or_ge 299172492347599357 n with h8 | h8
        · -- n > 299172492347599357
          rcases Nat.lt_or_ge 300019538224349231 n with h10 | h10
          · -- n > 300019538224349231
            rcases Nat.lt_or_ge 300868977253568117 n with h12 | h12
            · -- n > 300868977253568117
              exact RamareSaouter2003.prime_interval_nat_ladder_c06618 n (by omega) (by omega)
            · -- n <= 300868977253568117
              exact RamareSaouter2003.prime_interval_nat_ladder_c06617 n (by omega) (by omega)
          · -- n <= 300019538224349231
            exact RamareSaouter2003.prime_interval_nat_ladder_c06616 n (by omega) (by omega)
        · -- n <= 299172492347599357
          rcases Nat.lt_or_ge 297485583907704167 n with h10 | h10
          · -- n > 297485583907704167
            rcases Nat.lt_or_ge 298327854239127569 n with h12 | h12
            · -- n > 298327854239127569
              exact RamareSaouter2003.prime_interval_nat_ladder_c06615 n (by omega) (by omega)
            · -- n <= 298327854239127569
              exact RamareSaouter2003.prime_interval_nat_ladder_c06614 n (by omega) (by omega)
          · -- n <= 297485583907704167
            exact RamareSaouter2003.prime_interval_nat_ladder_c06613 n (by omega) (by omega)
    · -- n <= 296645691562227547
      rcases Nat.lt_or_ge 291655988866925237 n with h6 | h6
      · -- n > 291655988866925237
        rcases Nat.lt_or_ge 294140256220419533 n with h8 | h8
        · -- n > 294140256220419533
          rcases Nat.lt_or_ge 294973019745944279 n with h10 | h10
          · -- n > 294973019745944279
            rcases Nat.lt_or_ge 295808173341289607 n with h12 | h12
            · -- n > 295808173341289607
              exact RamareSaouter2003.prime_interval_nat_ladder_c06612 n (by omega) (by omega)
            · -- n <= 295808173341289607
              exact RamareSaouter2003.prime_interval_nat_ladder_c06611 n (by omega) (by omega)
          · -- n <= 294973019745944279
            exact RamareSaouter2003.prime_interval_nat_ladder_c06610 n (by omega) (by omega)
        · -- n <= 294140256220419533
          rcases Nat.lt_or_ge 292481717551354337 n with h10 | h10
          · -- n > 292481717551354337
            rcases Nat.lt_or_ge 293309817969889183 n with h12 | h12
            · -- n > 293309817969889183
              exact RamareSaouter2003.prime_interval_nat_ladder_c06609 n (by omega) (by omega)
            · -- n <= 293309817969889183
              exact RamareSaouter2003.prime_interval_nat_ladder_c06608 n (by omega) (by omega)
          · -- n <= 292481717551354337
            exact RamareSaouter2003.prime_interval_nat_ladder_c06607 n (by omega) (by omega)
      · -- n <= 291655988866925237
        rcases Nat.lt_or_ge 289192684046582663 n with h8 | h8
        · -- n > 289192684046582663
          rcases Nat.lt_or_ge 290011458156537527 n with h10 | h10
          · -- n > 290011458156537527
            rcases Nat.lt_or_ge 290832559874284993 n with h12 | h12
            · -- n > 290832559874284993
              exact RamareSaouter2003.prime_interval_nat_ladder_c06606 n (by omega) (by omega)
            · -- n <= 290832559874284993
              exact RamareSaouter2003.prime_interval_nat_ladder_c06605 n (by omega) (by omega)
          · -- n <= 290011458156537527
            exact RamareSaouter2003.prime_interval_nat_ladder_c06604 n (by omega) (by omega)
        · -- n <= 289192684046582663
          rcases Nat.lt_or_ge 287562089616332627 n with h10 | h10
          · -- n > 287562089616332627
            rcases Nat.lt_or_ge 288376213470619403 n with h12 | h12
            · -- n > 288376213470619403
              exact RamareSaouter2003.prime_interval_nat_ladder_c06603 n (by omega) (by omega)
            · -- n <= 288376213470619403
              exact RamareSaouter2003.prime_interval_nat_ladder_c06602 n (by omega) (by omega)
          · -- n <= 287562089616332627
            exact RamareSaouter2003.prime_interval_nat_ladder_c06601 n (by omega) (by omega)
