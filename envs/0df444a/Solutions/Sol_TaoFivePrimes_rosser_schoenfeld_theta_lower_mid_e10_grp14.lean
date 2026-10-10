-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp14
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T00:14:17.364868+00:00
-- url     : https://prove2.me/submissions/3d640fc2-6052-43dc-a344-8c38efceb836

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0651
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0652
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0653
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0654
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0655
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0656
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0657
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0658
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0659
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0660
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0661
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0662
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0663
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0664
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0665
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0666
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0667
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0668
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0669
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0670
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0671
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0672
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0673
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0674
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0675
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0676
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0677
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0678
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0679
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0680
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0681
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0682
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0683
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0684
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0685
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0686
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0687
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0688
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0689
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0690
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0691
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0692
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0693
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0694
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0695
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0696
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0697
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0698
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0699
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0700

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp14` (the range 5241435864 <= n <= 5577453187 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0651` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0700`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (5762916616992118131115 : Real) / 2 ^ 40 <= Chebyshev.theta (5241435864 : Real))
    (n : Nat) (h1 : 5241435864 <= n) (h2 : n <= 5577453187) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((6132360425961107643378 : Real) / 2 ^ 40 <= Chebyshev.theta (5577453188 : Real)) := by
  have hb0 := hbase
  have hb1 : (5770295359557171342256 : Real) / 2 ^ 40 <= Chebyshev.theta (5248143380 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0651 hb0 5241435864 le_rfl (by norm_num)).2
  have hb2 : (5777674523580363552763 : Real) / 2 ^ 40 <= Chebyshev.theta (5254856768 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0652 hb1 5248143380 le_rfl (by norm_num)).2
  have hb3 : (5785054108834881187025 : Real) / 2 ^ 40 <= Chebyshev.theta (5261557590 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0653 hb2 5254856768 le_rfl (by norm_num)).2
  have hb4 : (5792434114373279842240 : Real) / 2 ^ 40 <= Chebyshev.theta (5268271580 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0654 hb3 5261557590 le_rfl (by norm_num)).2
  have hb5 : (5799814540109039163479 : Real) / 2 ^ 40 <= Chebyshev.theta (5274989594 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0655 hb4 5268271580 le_rfl (by norm_num)).2
  have hb6 : (5807195385547969768605 : Real) / 2 ^ 40 <= Chebyshev.theta (5281700582 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0656 hb5 5274989594 le_rfl (by norm_num)).2
  have hb7 : (5814576649526977595970 : Real) / 2 ^ 40 <= Chebyshev.theta (5288404854 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0657 hb6 5281700582 le_rfl (by norm_num)).2
  have hb8 : (5821958331937958718232 : Real) / 2 ^ 40 <= Chebyshev.theta (5295121830 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0658 hb7 5288404854 le_rfl (by norm_num)).2
  have hb9 : (5829340432297701604739 : Real) / 2 ^ 40 <= Chebyshev.theta (5301831950 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0659 hb8 5295121830 le_rfl (by norm_num)).2
  have hb10 : (5836722950265520728876 : Real) / 2 ^ 40 <= Chebyshev.theta (5308553918 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0660 hb9 5301831950 le_rfl (by norm_num)).2
  have hb11 : (5844105885646791808371 : Real) / 2 ^ 40 <= Chebyshev.theta (5315271572 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0661 hb10 5308553918 le_rfl (by norm_num)).2
  have hb12 : (5851489237556030178468 : Real) / 2 ^ 40 <= Chebyshev.theta (5321985528 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0662 hb11 5315271572 le_rfl (by norm_num)).2
  have hb13 : (5858873005780935355351 : Real) / 2 ^ 40 <= Chebyshev.theta (5328702620 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0663 hb12 5321985528 le_rfl (by norm_num)).2
  have hb14 : (5866257189492772584488 : Real) / 2 ^ 40 <= Chebyshev.theta (5335426824 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0664 hb13 5328702620 le_rfl (by norm_num)).2
  have hb15 : (5873641788505848717018 : Real) / 2 ^ 40 <= Chebyshev.theta (5342137254 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0665 hb14 5335426824 le_rfl (by norm_num)).2
  have hb16 : (5881026802023246161190 : Real) / 2 ^ 40 <= Chebyshev.theta (5348858030 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0666 hb15 5342137254 le_rfl (by norm_num)).2
  have hb17 : (5888412229367129104081 : Real) / 2 ^ 40 <= Chebyshev.theta (5355570152 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0667 hb16 5348858030 le_rfl (by norm_num)).2
  have hb18 : (5895798069924598515285 : Real) / 2 ^ 40 <= Chebyshev.theta (5362279892 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0668 hb17 5355570152 le_rfl (by norm_num)).2
  have hb19 : (5903184323604296342608 : Real) / 2 ^ 40 <= Chebyshev.theta (5369004254 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0669 hb18 5362279892 le_rfl (by norm_num)).2
  have hb20 : (5910570989952595434826 : Real) / 2 ^ 40 <= Chebyshev.theta (5375726702 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0670 hb19 5369004254 le_rfl (by norm_num)).2
  have hb21 : (5917958068338920559988 : Real) / 2 ^ 40 <= Chebyshev.theta (5382442518 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0671 hb20 5375726702 le_rfl (by norm_num)).2
  have hb22 : (5925345558324901919783 : Real) / 2 ^ 40 <= Chebyshev.theta (5389167314 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0672 hb21 5382442518 le_rfl (by norm_num)).2
  have hb23 : (5932733459647257143833 : Real) / 2 ^ 40 <= Chebyshev.theta (5395888634 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0673 hb22 5389167314 le_rfl (by norm_num)).2
  have hb24 : (5940121771834310748811 : Real) / 2 ^ 40 <= Chebyshev.theta (5402609922 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0674 hb23 5395888634 le_rfl (by norm_num)).2
  have hb25 : (5947510494069608288627 : Real) / 2 ^ 40 <= Chebyshev.theta (5409335252 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0675 hb24 5402609922 le_rfl (by norm_num)).2
  have hb26 : (5954899626112009161154 : Real) / 2 ^ 40 <= Chebyshev.theta (5416047818 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0676 hb25 5409335252 le_rfl (by norm_num)).2
  have hb27 : (5962289166795070129715 : Real) / 2 ^ 40 <= Chebyshev.theta (5422772318 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0677 hb26 5416047818 le_rfl (by norm_num)).2
  have hb28 : (5969679116382817825805 : Real) / 2 ^ 40 <= Chebyshev.theta (5429493240 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0678 hb27 5422772318 le_rfl (by norm_num)).2
  have hb29 : (5977069474577175671795 : Real) / 2 ^ 40 <= Chebyshev.theta (5436226422 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0679 hb28 5429493240 le_rfl (by norm_num)).2
  have hb30 : (5984460240386787858941 : Real) / 2 ^ 40 <= Chebyshev.theta (5442940568 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0680 hb29 5436226422 le_rfl (by norm_num)).2
  have hb31 : (5991851413224618430676 : Real) / 2 ^ 40 <= Chebyshev.theta (5449657260 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0681 hb30 5442940568 le_rfl (by norm_num)).2
  have hb32 : (5999242992508655192977 : Real) / 2 ^ 40 <= Chebyshev.theta (5456381874 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0682 hb31 5449657260 le_rfl (by norm_num)).2
  have hb33 : (6006634977626743376556 : Real) / 2 ^ 40 <= Chebyshev.theta (5463091928 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0683 hb32 5456381874 le_rfl (by norm_num)).2
  have hb34 : (6014027368425193060614 : Real) / 2 ^ 40 <= Chebyshev.theta (5469823938 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0684 hb33 5463091928 le_rfl (by norm_num)).2
  have hb35 : (6021420164358460845893 : Real) / 2 ^ 40 <= Chebyshev.theta (5476540514 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0685 hb34 5469823938 le_rfl (by norm_num)).2
  have hb36 : (6028813365175730735738 : Real) / 2 ^ 40 <= Chebyshev.theta (5483275454 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0686 hb35 5476540514 le_rfl (by norm_num)).2
  have hb37 : (6036206970781179111247 : Real) / 2 ^ 40 <= Chebyshev.theta (5489998184 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0687 hb36 5483275454 le_rfl (by norm_num)).2
  have hb38 : (6043600980044645465230 : Real) / 2 ^ 40 <= Chebyshev.theta (5496719168 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0688 hb37 5489998184 le_rfl (by norm_num)).2
  have hb39 : (6050995392779134191870 : Real) / 2 ^ 40 <= Chebyshev.theta (5503449320 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0689 hb38 5496719168 le_rfl (by norm_num)).2
  have hb40 : (6058390208603211468359 : Real) / 2 ^ 40 <= Chebyshev.theta (5510175954 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0690 hb39 5503449320 le_rfl (by norm_num)).2
  have hb41 : (6065785426924631510306 : Real) / 2 ^ 40 <= Chebyshev.theta (5516903334 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0691 hb40 5510175954 le_rfl (by norm_num)).2
  have hb42 : (6073181047205851725470 : Real) / 2 ^ 40 <= Chebyshev.theta (5523631238 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0692 hb41 5516903334 le_rfl (by norm_num)).2
  have hb43 : (6080577069268063380330 : Real) / 2 ^ 40 <= Chebyshev.theta (5530365108 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0693 hb42 5523631238 le_rfl (by norm_num)).2
  have hb44 : (6087973492704899904634 : Real) / 2 ^ 40 <= Chebyshev.theta (5537096144 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0694 hb43 5530365108 le_rfl (by norm_num)).2
  have hb45 : (6095370316509003875608 : Real) / 2 ^ 40 <= Chebyshev.theta (5543816558 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0695 hb44 5537096144 le_rfl (by norm_num)).2
  have hb46 : (6102767540404068353315 : Real) / 2 ^ 40 <= Chebyshev.theta (5550550074 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0696 hb45 5543816558 le_rfl (by norm_num)).2
  have hb47 : (6110165163788916419953 : Real) / 2 ^ 40 <= Chebyshev.theta (5557269722 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0697 hb46 5550550074 le_rfl (by norm_num)).2
  have hb48 : (6117563185915751717537 : Real) / 2 ^ 40 <= Chebyshev.theta (5563990308 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0698 hb47 5557269722 le_rfl (by norm_num)).2
  have hb49 : (6124961606837974981260 : Real) / 2 ^ 40 <= Chebyshev.theta (5570724674 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0699 hb48 5563990308 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0700 hb49 5570724674 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 5409335252 with hc25 | hc25
  · rcases Nat.lt_or_ge n 5321985528 with hc12 | hc12
    · rcases Nat.lt_or_ge n 5281700582 with hc6 | hc6
      · rcases Nat.lt_or_ge n 5261557590 with hc3 | hc3
        · rcases Nat.lt_or_ge n 5248143380 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0651 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5254856768 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0652 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0653 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5268271580 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0654 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5274989594 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0655 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0656 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 5301831950 with hc9 | hc9
        · rcases Nat.lt_or_ge n 5288404854 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0657 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5295121830 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0658 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0659 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5308553918 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0660 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5315271572 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0661 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0662 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 5362279892 with hc18 | hc18
      · rcases Nat.lt_or_ge n 5342137254 with hc15 | hc15
        · rcases Nat.lt_or_ge n 5328702620 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0663 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5335426824 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0664 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0665 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5348858030 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0666 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5355570152 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0667 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0668 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 5382442518 with hc21 | hc21
        · rcases Nat.lt_or_ge n 5369004254 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0669 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5375726702 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0670 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0671 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5395888634 with hc23 | hc23
          · rcases Nat.lt_or_ge n 5389167314 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0672 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0673 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5402609922 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0674 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0675 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 5489998184 with hc37 | hc37
    · rcases Nat.lt_or_ge n 5449657260 with hc31 | hc31
      · rcases Nat.lt_or_ge n 5429493240 with hc28 | hc28
        · rcases Nat.lt_or_ge n 5416047818 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0676 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5422772318 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0677 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0678 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5436226422 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0679 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5442940568 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0680 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0681 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 5469823938 with hc34 | hc34
        · rcases Nat.lt_or_ge n 5456381874 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0682 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5463091928 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0683 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0684 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5476540514 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0685 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5483275454 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0686 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0687 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 5530365108 with hc43 | hc43
      · rcases Nat.lt_or_ge n 5510175954 with hc40 | hc40
        · rcases Nat.lt_or_ge n 5496719168 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0688 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5503449320 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0689 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0690 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5516903334 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0691 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5523631238 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0692 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0693 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 5550550074 with hc46 | hc46
        · rcases Nat.lt_or_ge n 5537096144 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0694 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5543816558 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0695 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0696 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5563990308 with hc48 | hc48
          · rcases Nat.lt_or_ge n 5557269722 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0697 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0698 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5570724674 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0699 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0700 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (5762916616992118131115 : Real) / 2 ^ 40 <= Chebyshev.theta (5241435864 : Real))
    (n : Nat) (h1 : 5241435864 <= n) (h2 : n <= 5577453187) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((6132360425961107643378 : Real) / 2 ^ 40 <= Chebyshev.theta (5577453188 : Real)) :=
  TFPLink.blk hbase n h1 h2
