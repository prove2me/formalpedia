-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp13
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T00:04:55.53477+00:00
-- url     : https://prove2.me/submissions/8559f5c2-b321-4f86-b545-5482dce6a7e1

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0601
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0602
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0603
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0604
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0605
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0606
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0607
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0608
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0609
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0610
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0611
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0612
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0613
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0614
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0615
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0616
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0617
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0618
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0619
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0620
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0621
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0622
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0623
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0624
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0625
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0626
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0627
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0628
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0629
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0630
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0631
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0632
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0633
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0634
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0635
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0636
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0637
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0638
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0639
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0640
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0641
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0642
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0643
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0644
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0645
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0646
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0647
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0648
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0649
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0650

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp13` (the range 4906374498 <= n <= 5241435863 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0601` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0650`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (5394528782830522203927 : Real) / 2 ^ 40 <= Chebyshev.theta (4906374498 : Real))
    (n : Nat) (h1 : 4906374498 <= n) (h2 : n <= 5241435863) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((5762916616992118131115 : Real) / 2 ^ 40 <= Chebyshev.theta (5241435864 : Real)) := by
  have hb0 := hbase
  have hb1 : (5401885759612225661699 : Real) / 2 ^ 40 <= Chebyshev.theta (4913069912 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0601 hb0 4906374498 le_rfl (by norm_num)).2
  have hb2 : (5409243185738787937031 : Real) / 2 ^ 40 <= Chebyshev.theta (4919760174 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0602 hb1 4913069912 le_rfl (by norm_num)).2
  have hb3 : (5416601060345191545905 : Real) / 2 ^ 40 <= Chebyshev.theta (4926451368 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0603 hb2 4919760174 le_rfl (by norm_num)).2
  have hb4 : (5423959382941526607610 : Real) / 2 ^ 40 <= Chebyshev.theta (4933150698 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0604 hb3 4926451368 le_rfl (by norm_num)).2
  have hb5 : (5431318152663519899246 : Real) / 2 ^ 40 <= Chebyshev.theta (4939834952 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0605 hb4 4933150698 le_rfl (by norm_num)).2
  have hb6 : (5438677368960046063173 : Real) / 2 ^ 40 <= Chebyshev.theta (4946532738 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0606 hb5 4939834952 le_rfl (by norm_num)).2
  have hb7 : (5446037031548471939954 : Real) / 2 ^ 40 <= Chebyshev.theta (4953221574 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0607 hb6 4946532738 le_rfl (by norm_num)).2
  have hb8 : (5453397139446558919537 : Real) / 2 ^ 40 <= Chebyshev.theta (4959912720 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0608 hb7 4953221574 le_rfl (by norm_num)).2
  have hb9 : (5460757692161978272579 : Real) / 2 ^ 40 <= Chebyshev.theta (4966611902 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0609 hb8 4959912720 le_rfl (by norm_num)).2
  have hb10 : (5468118689521503223941 : Real) / 2 ^ 40 <= Chebyshev.theta (4973303984 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0610 hb9 4966611902 le_rfl (by norm_num)).2
  have hb11 : (5475480130667000704943 : Real) / 2 ^ 40 <= Chebyshev.theta (4979999600 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0611 hb10 4973303984 le_rfl (by norm_num)).2
  have hb12 : (5482842015486087286816 : Real) / 2 ^ 40 <= Chebyshev.theta (4986702828 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0612 hb11 4979999600 le_rfl (by norm_num)).2
  have hb13 : (5490204343061089011465 : Real) / 2 ^ 40 <= Chebyshev.theta (4993401108 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0613 hb12 4986702828 le_rfl (by norm_num)).2
  have hb14 : (5497567113182124243706 : Real) / 2 ^ 40 <= Chebyshev.theta (5000109512 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0614 hb13 4993401108 le_rfl (by norm_num)).2
  have hb15 : (5504930325280205359076 : Real) / 2 ^ 40 <= Chebyshev.theta (5006800854 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0615 hb14 5000109512 le_rfl (by norm_num)).2
  have hb16 : (5512293977903651047548 : Real) / 2 ^ 40 <= Chebyshev.theta (5013488484 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0616 hb15 5006800854 le_rfl (by norm_num)).2
  have hb17 : (5519658070193583979325 : Real) / 2 ^ 40 <= Chebyshev.theta (5020179800 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0617 hb16 5013488484 le_rfl (by norm_num)).2
  have hb18 : (5527022602138654172361 : Real) / 2 ^ 40 <= Chebyshev.theta (5026868850 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0618 hb17 5020179800 le_rfl (by norm_num)).2
  have hb19 : (5534387573189782987092 : Real) / 2 ^ 40 <= Chebyshev.theta (5033571330 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0619 hb18 5026868850 le_rfl (by norm_num)).2
  have hb20 : (5541752983281847575721 : Real) / 2 ^ 40 <= Chebyshev.theta (5040274808 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0620 hb19 5033571330 le_rfl (by norm_num)).2
  have hb21 : (5549118832033041984880 : Real) / 2 ^ 40 <= Chebyshev.theta (5046981624 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0621 hb20 5040274808 le_rfl (by norm_num)).2
  have hb22 : (5556485118907126079284 : Real) / 2 ^ 40 <= Chebyshev.theta (5053690262 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0622 hb21 5046981624 le_rfl (by norm_num)).2
  have hb23 : (5563851842783614746272 : Real) / 2 ^ 40 <= Chebyshev.theta (5060386260 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0623 hb22 5053690262 le_rfl (by norm_num)).2
  have hb24 : (5571219003320892132830 : Real) / 2 ^ 40 <= Chebyshev.theta (5067090074 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0624 hb23 5060386260 le_rfl (by norm_num)).2
  have hb25 : (5578586600161340771916 : Real) / 2 ^ 40 <= Chebyshev.theta (5073792150 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0625 hb24 5067090074 le_rfl (by norm_num)).2
  have hb26 : (5585954631970128348978 : Real) / 2 ^ 40 <= Chebyshev.theta (5080488630 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0626 hb25 5073792150 le_rfl (by norm_num)).2
  have hb27 : (5593323098691249214911 : Real) / 2 ^ 40 <= Chebyshev.theta (5087193078 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0627 hb26 5080488630 le_rfl (by norm_num)).2
  have hb28 : (5600691999704919923970 : Real) / 2 ^ 40 <= Chebyshev.theta (5093888838 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0628 hb27 5087193078 le_rfl (by norm_num)).2
  have hb29 : (5608061334682363127422 : Real) / 2 ^ 40 <= Chebyshev.theta (5100601484 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0629 hb28 5093888838 le_rfl (by norm_num)).2
  have hb30 : (5615431103082687057997 : Real) / 2 ^ 40 <= Chebyshev.theta (5107299372 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0630 hb29 5100601484 le_rfl (by norm_num)).2
  have hb31 : (5622801303946725200289 : Real) / 2 ^ 40 <= Chebyshev.theta (5114002220 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0631 hb30 5107299372 le_rfl (by norm_num)).2
  have hb32 : (5630171936761309513662 : Real) / 2 ^ 40 <= Chebyshev.theta (5120704298 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0632 hb31 5114002220 le_rfl (by norm_num)).2
  have hb33 : (5637543001396194302521 : Real) / 2 ^ 40 <= Chebyshev.theta (5127407600 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0633 hb32 5120704298 le_rfl (by norm_num)).2
  have hb34 : (5644914496925332671199 : Real) / 2 ^ 40 <= Chebyshev.theta (5134115084 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0634 hb33 5127407600 le_rfl (by norm_num)).2
  have hb35 : (5652286423255505914707 : Real) / 2 ^ 40 <= Chebyshev.theta (5140816608 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0635 hb34 5134115084 le_rfl (by norm_num)).2
  have hb36 : (5659658779447456502538 : Real) / 2 ^ 40 <= Chebyshev.theta (5147526120 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0636 hb35 5140816608 le_rfl (by norm_num)).2
  have hb37 : (5667031564849397760888 : Real) / 2 ^ 40 <= Chebyshev.theta (5154223904 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0637 hb36 5147526120 le_rfl (by norm_num)).2
  have hb38 : (5674404779114504008919 : Real) / 2 ^ 40 <= Chebyshev.theta (5160932264 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0638 hb37 5154223904 le_rfl (by norm_num)).2
  have hb39 : (5681778422246682617500 : Real) / 2 ^ 40 <= Chebyshev.theta (5167639470 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0639 hb38 5160932264 le_rfl (by norm_num)).2
  have hb40 : (5689152493133635346264 : Real) / 2 ^ 40 <= Chebyshev.theta (5174345822 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0640 hb39 5167639470 le_rfl (by norm_num)).2
  have hb41 : (5696526991237261407131 : Real) / 2 ^ 40 <= Chebyshev.theta (5181056184 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0641 hb40 5174345822 le_rfl (by norm_num)).2
  have hb42 : (5703901916544536230542 : Real) / 2 ^ 40 <= Chebyshev.theta (5187763982 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0642 hb41 5181056184 le_rfl (by norm_num)).2
  have hb43 : (5711277267891807559011 : Real) / 2 ^ 40 <= Chebyshev.theta (5194465824 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0643 hb42 5187763982 le_rfl (by norm_num)).2
  have hb44 : (5718653044660966534308 : Real) / 2 ^ 40 <= Chebyshev.theta (5201172942 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0644 hb43 5194465824 le_rfl (by norm_num)).2
  have hb45 : (5726029246603616008409 : Real) / 2 ^ 40 <= Chebyshev.theta (5207881194 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0645 hb44 5201172942 le_rfl (by norm_num)).2
  have hb46 : (5733405873291433708092 : Real) / 2 ^ 40 <= Chebyshev.theta (5214588074 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0646 hb45 5207881194 le_rfl (by norm_num)).2
  have hb47 : (5740782924081750158243 : Real) / 2 ^ 40 <= Chebyshev.theta (5221299804 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0647 hb46 5214588074 le_rfl (by norm_num)).2
  have hb48 : (5748160398744216542942 : Real) / 2 ^ 40 <= Chebyshev.theta (5228011688 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0648 hb47 5221299804 le_rfl (by norm_num)).2
  have hb49 : (5755538296529361916689 : Real) / 2 ^ 40 <= Chebyshev.theta (5234718192 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0649 hb48 5228011688 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0650 hb49 5234718192 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 5073792150 with hc25 | hc25
  · rcases Nat.lt_or_ge n 4986702828 with hc12 | hc12
    · rcases Nat.lt_or_ge n 4946532738 with hc6 | hc6
      · rcases Nat.lt_or_ge n 4926451368 with hc3 | hc3
        · rcases Nat.lt_or_ge n 4913069912 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0601 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4919760174 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0602 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0603 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4933150698 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0604 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4939834952 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0605 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0606 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 4966611902 with hc9 | hc9
        · rcases Nat.lt_or_ge n 4953221574 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0607 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4959912720 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0608 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0609 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4973303984 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0610 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 4979999600 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0611 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0612 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 5026868850 with hc18 | hc18
      · rcases Nat.lt_or_ge n 5006800854 with hc15 | hc15
        · rcases Nat.lt_or_ge n 4993401108 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0613 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5000109512 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0614 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0615 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5013488484 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0616 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5020179800 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0617 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0618 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 5046981624 with hc21 | hc21
        · rcases Nat.lt_or_ge n 5033571330 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0619 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5040274808 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0620 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0621 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5060386260 with hc23 | hc23
          · rcases Nat.lt_or_ge n 5053690262 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0622 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0623 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5067090074 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0624 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0625 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 5154223904 with hc37 | hc37
    · rcases Nat.lt_or_ge n 5114002220 with hc31 | hc31
      · rcases Nat.lt_or_ge n 5093888838 with hc28 | hc28
        · rcases Nat.lt_or_ge n 5080488630 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0626 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5087193078 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0627 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0628 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5100601484 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0629 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5107299372 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0630 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0631 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 5134115084 with hc34 | hc34
        · rcases Nat.lt_or_ge n 5120704298 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0632 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5127407600 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0633 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0634 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5140816608 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0635 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5147526120 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0636 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0637 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 5194465824 with hc43 | hc43
      · rcases Nat.lt_or_ge n 5174345822 with hc40 | hc40
        · rcases Nat.lt_or_ge n 5160932264 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0638 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5167639470 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0639 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0640 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5181056184 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0641 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5187763982 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0642 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0643 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 5214588074 with hc46 | hc46
        · rcases Nat.lt_or_ge n 5201172942 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0644 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5207881194 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0645 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0646 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5228011688 with hc48 | hc48
          · rcases Nat.lt_or_ge n 5221299804 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0647 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0648 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5234718192 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0649 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0650 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (5394528782830522203927 : Real) / 2 ^ 40 <= Chebyshev.theta (4906374498 : Real))
    (n : Nat) (h1 : 4906374498 <= n) (h2 : n <= 5241435863) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((5762916616992118131115 : Real) / 2 ^ 40 <= Chebyshev.theta (5241435864 : Real)) :=
  TFPLink.blk hbase n h1 h2
