-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp173
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T16:04:36.236609+00:00
-- url     : https://prove2.me/submissions/6f8ff5be-c441-408d-bf0a-4e6bf376e3a2

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08571
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08572
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08573
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08574
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08575
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08576
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08577
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08578
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08579
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08580
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08581
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08582
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08583
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08584
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08585
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08586
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08587
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08588
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08589
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08590
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08591
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08592
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08593
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08594
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08595
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08596
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08597
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08598
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08599
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08600
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08601
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08602
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08603
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08604
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08605
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08606
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08607
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08608
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08609
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08610
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08611
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08612
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08613
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08614
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08615
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08616
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08617
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08618
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08619

theorem solution (n : Nat)
    (hn : 62115373307991419869 < n) (hupper : n <= 70010134047899070677) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 65864256099870520631 n with h2 | h2
  · -- n > 65864256099870520631
    rcases Nat.lt_or_ge 67822707016936633637 n with h4 | h4
    · -- n > 67822707016936633637
      rcases Nat.lt_or_ge 68823664737971126953 n with h6 | h6
      · -- n > 68823664737971126953
        rcases Nat.lt_or_ge 69329669147789802887 n with h8 | h8
        · -- n > 69329669147789802887
          rcases Nat.lt_or_ge 69669070977098876993 n with h10 | h10
          · -- n > 69669070977098876993
            rcases Nat.lt_or_ge 69839394359624347649 n with h12 | h12
            · -- n > 69839394359624347649
              exact RamareSaouter2003.prime_interval_nat_ladder_c08619 n (by omega) (by omega)
            · -- n <= 69839394359624347649
              exact RamareSaouter2003.prime_interval_nat_ladder_c08618 n (by omega) (by omega)
          · -- n <= 69669070977098876993
            rcases Nat.lt_or_ge 69499162920005455411 n with h12 | h12
            · -- n > 69499162920005455411
              exact RamareSaouter2003.prime_interval_nat_ladder_c08617 n (by omega) (by omega)
            · -- n <= 69499162920005455411
              exact RamareSaouter2003.prime_interval_nat_ladder_c08616 n (by omega) (by omega)
        · -- n <= 69329669147789802887
          rcases Nat.lt_or_ge 68991920787277761569 n with h10 | h10
          · -- n > 68991920787277761569
            rcases Nat.lt_or_ge 69160588566536850389 n with h12 | h12
            · -- n > 69160588566536850389
              exact RamareSaouter2003.prime_interval_nat_ladder_c08615 n (by omega) (by omega)
            · -- n <= 69160588566536850389
              exact RamareSaouter2003.prime_interval_nat_ladder_c08614 n (by omega) (by omega)
          · -- n <= 68991920787277761569
            exact RamareSaouter2003.prime_interval_nat_ladder_c08613 n (by omega) (by omega)
      · -- n <= 68823664737971126953
        rcases Nat.lt_or_ge 68321352643794706367 n with h8 | h8
        · -- n > 68321352643794706367
          rcases Nat.lt_or_ge 68488381341659357747 n with h10 | h10
          · -- n > 68488381341659357747
            rcases Nat.lt_or_ge 68655818423723518297 n with h12 | h12
            · -- n > 68655818423723518297
              exact RamareSaouter2003.prime_interval_nat_ladder_c08612 n (by omega) (by omega)
            · -- n <= 68655818423723518297
              exact RamareSaouter2003.prime_interval_nat_ladder_c08611 n (by omega) (by omega)
          · -- n <= 68488381341659357747
            exact RamareSaouter2003.prime_interval_nat_ladder_c08610 n (by omega) (by omega)
        · -- n <= 68321352643794706367
          rcases Nat.lt_or_ge 67988516523756891583 n with h10 | h10
          · -- n > 67988516523756891583
            rcases Nat.lt_or_ge 68154731633242085879 n with h12 | h12
            · -- n > 68154731633242085879
              exact RamareSaouter2003.prime_interval_nat_ladder_c08609 n (by omega) (by omega)
            · -- n <= 68154731633242085879
              exact RamareSaouter2003.prime_interval_nat_ladder_c08608 n (by omega) (by omega)
          · -- n <= 67988516523756891583
            exact RamareSaouter2003.prime_interval_nat_ladder_c08607 n (by omega) (by omega)
    · -- n <= 67822707016936633637
      rcases Nat.lt_or_ge 66836309076000995621 n with h6 | h6
      · -- n > 66836309076000995621
        rcases Nat.lt_or_ge 67327702435411350161 n with h8 | h8
        · -- n > 67327702435411350161
          rcases Nat.lt_or_ge 67492302027545894561 n with h10 | h10
          · -- n > 67492302027545894561
            rcases Nat.lt_or_ge 67657303639901052677 n with h12 | h12
            · -- n > 67657303639901052677
              exact RamareSaouter2003.prime_interval_nat_ladder_c08606 n (by omega) (by omega)
            · -- n <= 67657303639901052677
              exact RamareSaouter2003.prime_interval_nat_ladder_c08605 n (by omega) (by omega)
          · -- n <= 67492302027545894561
            exact RamareSaouter2003.prime_interval_nat_ladder_c08604 n (by omega) (by omega)
        · -- n <= 67327702435411350161
          rcases Nat.lt_or_ge 66999707168145790187 n with h10 | h10
          · -- n > 66999707168145790187
            rcases Nat.lt_or_ge 67163504716091806741 n with h12 | h12
            · -- n > 67163504716091806741
              exact RamareSaouter2003.prime_interval_nat_ladder_c08603 n (by omega) (by omega)
            · -- n <= 67163504716091806741
              exact RamareSaouter2003.prime_interval_nat_ladder_c08602 n (by omega) (by omega)
          · -- n <= 66999707168145790187
            exact RamareSaouter2003.prime_interval_nat_ladder_c08601 n (by omega) (by omega)
      · -- n <= 66836309076000995621
        rcases Nat.lt_or_ge 66348502961092481887 n with h8 | h8
        · -- n > 66348502961092481887
          rcases Nat.lt_or_ge 66510708093684751597 n with h10 | h10
          · -- n > 66510708093684751597
            rcases Nat.lt_or_ge 66673310313915215177 n with h12 | h12
            · -- n > 66673310313915215177
              exact RamareSaouter2003.prime_interval_nat_ladder_c08600 n (by omega) (by omega)
            · -- n <= 66673310313915215177
              exact RamareSaouter2003.prime_interval_nat_ladder_c08599 n (by omega) (by omega)
          · -- n <= 66510708093684751597
            exact RamareSaouter2003.prime_interval_nat_ladder_c08598 n (by omega) (by omega)
        · -- n <= 66348502961092481887
          rcases Nat.lt_or_ge 66025277768075077021 n with h10 | h10
          · -- n > 66025277768075077021
            rcases Nat.lt_or_ge 66186693098579703457 n with h12 | h12
            · -- n > 66186693098579703457
              exact RamareSaouter2003.prime_interval_nat_ladder_c08597 n (by omega) (by omega)
            · -- n <= 66186693098579703457
              exact RamareSaouter2003.prime_interval_nat_ladder_c08596 n (by omega) (by omega)
          · -- n <= 66025277768075077021
            exact RamareSaouter2003.prime_interval_nat_ladder_c08595 n (by omega) (by omega)
  · -- n <= 65864256099870520631
    rcases Nat.lt_or_ge 63962354878037902327 n with h4 | h4
    · -- n > 63962354878037902327
      rcases Nat.lt_or_ge 64906339640252325991 n with h6 | h6
      · -- n > 64906339640252325991
        rcases Nat.lt_or_ge 65383543484683483769 n with h8 | h8
        · -- n > 65383543484683483769
          rcases Nat.lt_or_ge 65543389968248366627 n with h10 | h10
          · -- n > 65543389968248366627
            rcases Nat.lt_or_ge 65703626987151591719 n with h12 | h12
            · -- n > 65703626987151591719
              exact RamareSaouter2003.prime_interval_nat_ladder_c08594 n (by omega) (by omega)
            · -- n <= 65703626987151591719
              exact RamareSaouter2003.prime_interval_nat_ladder_c08593 n (by omega) (by omega)
          · -- n <= 65543389968248366627
            exact RamareSaouter2003.prime_interval_nat_ladder_c08592 n (by omega) (by omega)
        · -- n <= 65383543484683483769
          rcases Nat.lt_or_ge 65065019638502839051 n with h10 | h10
          · -- n > 65065019638502839051
            rcases Nat.lt_or_ge 65224086772185410623 n with h12 | h12
            · -- n > 65224086772185410623
              exact RamareSaouter2003.prime_interval_nat_ladder_c08591 n (by omega) (by omega)
            · -- n <= 65224086772185410623
              exact RamareSaouter2003.prime_interval_nat_ladder_c08590 n (by omega) (by omega)
          · -- n <= 65065019638502839051
            exact RamareSaouter2003.prime_interval_nat_ladder_c08589 n (by omega) (by omega)
      · -- n <= 64906339640252325991
        rcases Nat.lt_or_ge 64432619096397022963 n with h8 | h8
        · -- n > 64432619096397022963
          rcases Nat.lt_or_ge 64590139883952941579 n with h10 | h10
          · -- n > 64590139883952941579
            rcases Nat.lt_or_ge 64748046716381710277 n with h12 | h12
            · -- n > 64748046716381710277
              exact RamareSaouter2003.prime_interval_nat_ladder_c08588 n (by omega) (by omega)
            · -- n <= 64748046716381710277
              exact RamareSaouter2003.prime_interval_nat_ladder_c08587 n (by omega) (by omega)
          · -- n <= 64590139883952941579
            exact RamareSaouter2003.prime_interval_nat_ladder_c08586 n (by omega) (by omega)
        · -- n <= 64432619096397022963
          rcases Nat.lt_or_ge 64118726956889107007 n with h10 | h10
          · -- n > 64118726956889107007
            rcases Nat.lt_or_ge 64275481414091128073 n with h12 | h12
            · -- n > 64275481414091128073
              exact RamareSaouter2003.prime_interval_nat_ladder_c08585 n (by omega) (by omega)
            · -- n <= 64275481414091128073
              exact RamareSaouter2003.prime_interval_nat_ladder_c08584 n (by omega) (by omega)
          · -- n <= 64118726956889107007
            exact RamareSaouter2003.prime_interval_nat_ladder_c08583 n (by omega) (by omega)
    · -- n <= 63962354878037902327
      rcases Nat.lt_or_ge 63032098736351056667 n with h6 | h6
      · -- n > 63032098736351056667
        rcases Nat.lt_or_ge 63495523048948773763 n with h8 | h8
        · -- n > 63495523048948773763
          rcases Nat.lt_or_ge 63650753956274290991 n with h10 | h10
          · -- n > 63650753956274290991
            rcases Nat.lt_or_ge 63806364045984351887 n with h12 | h12
            · -- n > 63806364045984351887
              exact RamareSaouter2003.prime_interval_nat_ladder_c08582 n (by omega) (by omega)
            · -- n <= 63806364045984351887
              exact RamareSaouter2003.prime_interval_nat_ladder_c08581 n (by omega) (by omega)
          · -- n <= 63650753956274290991
            exact RamareSaouter2003.prime_interval_nat_ladder_c08580 n (by omega) (by omega)
        · -- n <= 63495523048948773763
          rcases Nat.lt_or_ge 63186196138069961843 n with h10 | h10
          · -- n > 63186196138069961843
            rcases Nat.lt_or_ge 63340670742195558323 n with h12 | h12
            · -- n > 63340670742195558323
              exact RamareSaouter2003.prime_interval_nat_ladder_c08579 n (by omega) (by omega)
            · -- n <= 63340670742195558323
              exact RamareSaouter2003.prime_interval_nat_ladder_c08578 n (by omega) (by omega)
          · -- n <= 63186196138069961843
            exact RamareSaouter2003.prime_interval_nat_ladder_c08577 n (by omega) (by omega)
      · -- n <= 63032098736351056667
        rcases Nat.lt_or_ge 62572057224258429049 n with h8 | h8
        · -- n > 62572057224258429049
          rcases Nat.lt_or_ge 62725029743759495257 n with h10 | h10
          · -- n > 62725029743759495257
            rcases Nat.lt_or_ge 62878376875450952941 n with h12 | h12
            · -- n > 62878376875450952941
              exact RamareSaouter2003.prime_interval_nat_ladder_c08576 n (by omega) (by omega)
            · -- n <= 62878376875450952941
              exact RamareSaouter2003.prime_interval_nat_ladder_c08575 n (by omega) (by omega)
          · -- n <= 62725029743759495257
            exact RamareSaouter2003.prime_interval_nat_ladder_c08574 n (by omega) (by omega)
        · -- n <= 62572057224258429049
          rcases Nat.lt_or_ge 62267229616791536177 n with h10 | h10
          · -- n > 62267229616791536177
            rcases Nat.lt_or_ge 62419457367705832123 n with h12 | h12
            · -- n > 62419457367705832123
              exact RamareSaouter2003.prime_interval_nat_ladder_c08573 n (by omega) (by omega)
            · -- n <= 62419457367705832123
              exact RamareSaouter2003.prime_interval_nat_ladder_c08572 n (by omega) (by omega)
          · -- n <= 62267229616791536177
            exact RamareSaouter2003.prime_interval_nat_ladder_c08571 n (by omega) (by omega)
