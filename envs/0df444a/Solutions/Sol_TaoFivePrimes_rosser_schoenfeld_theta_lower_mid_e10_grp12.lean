-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp12
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T00:01:27.738833+00:00
-- url     : https://prove2.me/submissions/ac0c28d6-b9d7-4910-a076-72f4b3ec1dd7

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0551
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0552
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0553
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0554
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0555
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0556
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0557
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0558
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0559
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0560
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0561
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0562
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0563
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0564
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0565
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0566
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0567
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0568
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0569
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0570
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0571
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0572
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0573
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0574
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0575
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0576
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0577
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0578
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0579
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0580
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0581
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0582
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0583
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0584
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0585
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0586
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0587
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0588
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0589
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0590
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0591
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0592
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0593
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0594
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0595
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0596
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0597
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0598
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0599
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0600

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp12` (the range 4572345230 <= n <= 4906374497 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0551` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0600`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (5027265814990202898813 : Real) / 2 ^ 40 <= Chebyshev.theta (4572345230 : Real))
    (n : Nat) (h1 : 4572345230 <= n) (h2 : n <= 4906374497) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((5394528782830522203927 : Real) / 2 ^ 40 <= Chebyshev.theta (4906374498 : Real)) := by
  have hb0 := hbase
  have hb1 : (5034599561105170740718 : Real) / 2 ^ 40 <= Chebyshev.theta (4579020054 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0551 hb0 4572345230 le_rfl (by norm_num)).2
  have hb2 : (5041933788015611580368 : Real) / 2 ^ 40 <= Chebyshev.theta (4585696658 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0552 hb1 4579020054 le_rfl (by norm_num)).2
  have hb3 : (5049268494667279544574 : Real) / 2 ^ 40 <= Chebyshev.theta (4592368700 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0553 hb2 4585696658 le_rfl (by norm_num)).2
  have hb4 : (5056603679876055195115 : Real) / 2 ^ 40 <= Chebyshev.theta (4599025518 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0554 hb3 4592368700 le_rfl (by norm_num)).2
  have hb5 : (5063939343275389931535 : Real) / 2 ^ 40 <= Chebyshev.theta (4605706410 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0555 hb4 4599025518 le_rfl (by norm_num)).2
  have hb6 : (5071275484312855939239 : Real) / 2 ^ 40 <= Chebyshev.theta (4612377140 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0556 hb5 4605706410 le_rfl (by norm_num)).2
  have hb7 : (5078612102689260248922 : Real) / 2 ^ 40 <= Chebyshev.theta (4619052960 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0557 hb6 4612377140 le_rfl (by norm_num)).2
  have hb8 : (5085949197124659803461 : Real) / 2 ^ 40 <= Chebyshev.theta (4625715974 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0558 hb7 4619052960 le_rfl (by norm_num)).2
  have hb9 : (5093286766853768108606 : Real) / 2 ^ 40 <= Chebyshev.theta (4632391910 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0559 hb8 4625715974 le_rfl (by norm_num)).2
  have hb10 : (5100624811692752668290 : Real) / 2 ^ 40 <= Chebyshev.theta (4639073382 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0560 hb9 4632391910 le_rfl (by norm_num)).2
  have hb11 : (5107963331067416030227 : Real) / 2 ^ 40 <= Chebyshev.theta (4645743578 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0561 hb10 4639073382 le_rfl (by norm_num)).2
  have hb12 : (5115302324051525233469 : Real) / 2 ^ 40 <= Chebyshev.theta (4652422082 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0562 hb11 4645743578 le_rfl (by norm_num)).2
  have hb13 : (5122641790556327139734 : Real) / 2 ^ 40 <= Chebyshev.theta (4659100164 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0563 hb12 4652422082 le_rfl (by norm_num)).2
  have hb14 : (5129981729359744993798 : Real) / 2 ^ 40 <= Chebyshev.theta (4665776982 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0564 hb13 4659100164 le_rfl (by norm_num)).2
  have hb15 : (5137322140035875371071 : Real) / 2 ^ 40 <= Chebyshev.theta (4672453692 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0565 hb14 4665776982 le_rfl (by norm_num)).2
  have hb16 : (5144663021438928280891 : Real) / 2 ^ 40 <= Chebyshev.theta (4679124522 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0566 hb15 4672453692 le_rfl (by norm_num)).2
  have hb17 : (5152004372831154890362 : Real) / 2 ^ 40 <= Chebyshev.theta (4685795624 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0567 hb16 4679124522 le_rfl (by norm_num)).2
  have hb18 : (5159346193772882944217 : Real) / 2 ^ 40 <= Chebyshev.theta (4692463740 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0568 hb17 4685795624 le_rfl (by norm_num)).2
  have hb19 : (5166688483661447002418 : Real) / 2 ^ 40 <= Chebyshev.theta (4699143584 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0569 hb18 4692463740 le_rfl (by norm_num)).2
  have hb20 : (5174031242007867510652 : Real) / 2 ^ 40 <= Chebyshev.theta (4705822350 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0570 hb19 4699143584 le_rfl (by norm_num)).2
  have hb21 : (5181374468765256018505 : Real) / 2 ^ 40 <= Chebyshev.theta (4712510864 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0571 hb20 4705822350 le_rfl (by norm_num)).2
  have hb22 : (5188718162774425835198 : Real) / 2 ^ 40 <= Chebyshev.theta (4719179478 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0572 hb21 4712510864 le_rfl (by norm_num)).2
  have hb23 : (5196062323082908795385 : Real) / 2 ^ 40 <= Chebyshev.theta (4725868118 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0573 hb22 4719179478 le_rfl (by norm_num)).2
  have hb24 : (5203406949513570753059 : Real) / 2 ^ 40 <= Chebyshev.theta (4732542012 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0574 hb23 4725868118 le_rfl (by norm_num)).2
  have hb25 : (5210752041328662875324 : Real) / 2 ^ 40 <= Chebyshev.theta (4739225064 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0575 hb24 4732542012 le_rfl (by norm_num)).2
  have hb26 : (5218097597738338051046 : Real) / 2 ^ 40 <= Chebyshev.theta (4745900262 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0576 hb25 4739225064 le_rfl (by norm_num)).2
  have hb27 : (5225443617876648469810 : Real) / 2 ^ 40 <= Chebyshev.theta (4752572598 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0577 hb26 4745900262 le_rfl (by norm_num)).2
  have hb28 : (5232790100757262085416 : Real) / 2 ^ 40 <= Chebyshev.theta (4759247348 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0578 hb27 4752572598 le_rfl (by norm_num)).2
  have hb29 : (5240137046788406120909 : Real) / 2 ^ 40 <= Chebyshev.theta (4765941648 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0579 hb28 4759247348 le_rfl (by norm_num)).2
  have hb30 : (5247484455592554124348 : Real) / 2 ^ 40 <= Chebyshev.theta (4772629788 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0580 hb29 4765941648 le_rfl (by norm_num)).2
  have hb31 : (5254832326464704752015 : Real) / 2 ^ 40 <= Chebyshev.theta (4779314994 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0581 hb30 4772629788 le_rfl (by norm_num)).2
  have hb32 : (5262180658643478880527 : Real) / 2 ^ 40 <= Chebyshev.theta (4785996852 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0582 hb31 4779314994 le_rfl (by norm_num)).2
  have hb33 : (5269529451250090195189 : Real) / 2 ^ 40 <= Chebyshev.theta (4792683432 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0583 hb32 4785996852 le_rfl (by norm_num)).2
  have hb34 : (5276878703454873615071 : Real) / 2 ^ 40 <= Chebyshev.theta (4799366744 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0584 hb33 4792683432 le_rfl (by norm_num)).2
  have hb35 : (5284228414829506866951 : Real) / 2 ^ 40 <= Chebyshev.theta (4806051360 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0585 hb34 4799366744 le_rfl (by norm_num)).2
  have hb36 : (5291578585004278240624 : Real) / 2 ^ 40 <= Chebyshev.theta (4812735494 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0586 hb35 4806051360 le_rfl (by norm_num)).2
  have hb37 : (5298929212615887433787 : Real) / 2 ^ 40 <= Chebyshev.theta (4819415334 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0587 hb36 4812735494 le_rfl (by norm_num)).2
  have hb38 : (5306280298023254370439 : Real) / 2 ^ 40 <= Chebyshev.theta (4826109932 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0588 hb37 4819415334 le_rfl (by norm_num)).2
  have hb39 : (5313631840396900034931 : Real) / 2 ^ 40 <= Chebyshev.theta (4832797262 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0589 hb38 4826109932 le_rfl (by norm_num)).2
  have hb40 : (5320983839064756638001 : Real) / 2 ^ 40 <= Chebyshev.theta (4839487172 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0590 hb39 4832797262 le_rfl (by norm_num)).2
  have hb41 : (5328336293379875203110 : Real) / 2 ^ 40 <= Chebyshev.theta (4846174722 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0591 hb40 4839487172 le_rfl (by norm_num)).2
  have hb42 : (5335689202621997033627 : Real) / 2 ^ 40 <= Chebyshev.theta (4852861044 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0592 hb41 4846174722 le_rfl (by norm_num)).2
  have hb43 : (5343042566214319763353 : Real) / 2 ^ 40 <= Chebyshev.theta (4859551058 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0593 hb42 4852861044 le_rfl (by norm_num)).2
  have hb44 : (5350396383945473234869 : Real) / 2 ^ 40 <= Chebyshev.theta (4866246038 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0594 hb43 4859551058 le_rfl (by norm_num)).2
  have hb45 : (5357750654939276047390 : Real) / 2 ^ 40 <= Chebyshev.theta (4872927000 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0595 hb44 4866246038 le_rfl (by norm_num)).2
  have hb46 : (5365105378186696190628 : Real) / 2 ^ 40 <= Chebyshev.theta (4879620134 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0596 hb45 4872927000 le_rfl (by norm_num)).2
  have hb47 : (5372460552955938920628 : Real) / 2 ^ 40 <= Chebyshev.theta (4886293968 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0597 hb46 4879620134 le_rfl (by norm_num)).2
  have hb48 : (5379816178963254686275 : Real) / 2 ^ 40 <= Chebyshev.theta (4892986688 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0598 hb47 4886293968 le_rfl (by norm_num)).2
  have hb49 : (5387172255543646178927 : Real) / 2 ^ 40 <= Chebyshev.theta (4899680432 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0599 hb48 4892986688 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0600 hb49 4899680432 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 4739225064 with hc25 | hc25
  · rcases Nat.lt_or_ge n 4652422082 with hc12 | hc12
    · rcases Nat.lt_or_ge n 4612377140 with hc6 | hc6
      · rcases Nat.lt_or_ge n 4592368700 with hc3 | hc3
        · rcases Nat.lt_or_ge n 4579020054 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0551 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4585696658 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0552 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0553 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4599025518 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0554 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4605706410 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0555 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0556 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 4632391910 with hc9 | hc9
        · rcases Nat.lt_or_ge n 4619052960 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0557 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4625715974 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0558 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0559 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4639073382 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0560 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4645743578 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0561 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0562 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 4692463740 with hc18 | hc18
      · rcases Nat.lt_or_ge n 4672453692 with hc15 | hc15
        · rcases Nat.lt_or_ge n 4659100164 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0563 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4665776982 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0564 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0565 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4679124522 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0566 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4685795624 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0567 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0568 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 4712510864 with hc21 | hc21
        · rcases Nat.lt_or_ge n 4699143584 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0569 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4705822350 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0570 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0571 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4725868118 with hc23 | hc23
          · rcases Nat.lt_or_ge n 4719179478 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0572 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0573 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4732542012 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0574 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0575 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 4819415334 with hc37 | hc37
    · rcases Nat.lt_or_ge n 4779314994 with hc31 | hc31
      · rcases Nat.lt_or_ge n 4759247348 with hc28 | hc28
        · rcases Nat.lt_or_ge n 4745900262 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0576 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4752572598 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0577 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0578 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4765941648 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0579 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4772629788 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0580 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0581 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 4799366744 with hc34 | hc34
        · rcases Nat.lt_or_ge n 4785996852 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0582 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4792683432 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0583 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0584 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4806051360 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0585 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4812735494 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0586 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0587 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 4859551058 with hc43 | hc43
      · rcases Nat.lt_or_ge n 4839487172 with hc40 | hc40
        · rcases Nat.lt_or_ge n 4826109932 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0588 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4832797262 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0589 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0590 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4846174722 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0591 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4852861044 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0592 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0593 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 4879620134 with hc46 | hc46
        · rcases Nat.lt_or_ge n 4866246038 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0594 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4872927000 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0595 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0596 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4892986688 with hc48 | hc48
          · rcases Nat.lt_or_ge n 4886293968 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0597 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0598 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4899680432 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0599 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0600 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (5027265814990202898813 : Real) / 2 ^ 40 <= Chebyshev.theta (4572345230 : Real))
    (n : Nat) (h1 : 4572345230 <= n) (h2 : n <= 4906374497) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((5394528782830522203927 : Real) / 2 ^ 40 <= Chebyshev.theta (4906374498 : Real)) :=
  TFPLink.blk hbase n h1 h2
