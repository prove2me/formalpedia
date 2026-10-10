-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp16
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T00:20:48.389711+00:00
-- url     : https://prove2.me/submissions/57e6fa93-d918-4cb8-aa68-d4f56d9c6145

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0751
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0752
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0753
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0754
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0755
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0756
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0757
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0758
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0759
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0760
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0761
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0762
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0763
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0764
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0765
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0766
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0767
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0768
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0769
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0770
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0771
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0772
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0773
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0774
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0775
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0776
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0777
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0778
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0779
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0780
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0781
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0782
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0783
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0784
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0785
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0786
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0787
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0788
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0789
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0790
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0791
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0792
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0793
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0794
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0795
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0796
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0797
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0798
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0799
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0800

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp16` (the range 5914357088 <= n <= 6252112019 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0751` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0800`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (6502799203779927993439 : Real) / 2 ^ 40 <= Chebyshev.theta (5914357088 : Real))
    (n : Nat) (h1 : 5914357088 <= n) (h2 : n <= 6252112019) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((6874178730578669503809 : Real) / 2 ^ 40 <= Chebyshev.theta (6252112020 : Real)) := by
  have hb0 := hbase
  have hb1 : (6510217746663880191950 : Real) / 2 ^ 40 <= Chebyshev.theta (5921103128 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0751 hb0 5914357088 le_rfl (by norm_num)).2
  have hb2 : (6517636665308524829814 : Real) / 2 ^ 40 <= Chebyshev.theta (5927850158 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0752 hb1 5921103128 le_rfl (by norm_num)).2
  have hb3 : (6525055958979090118606 : Real) / 2 ^ 40 <= Chebyshev.theta (5934592460 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0753 hb2 5927850158 le_rfl (by norm_num)).2
  have hb4 : (6532475627543469709938 : Real) / 2 ^ 40 <= Chebyshev.theta (5941346624 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0754 hb3 5934592460 le_rfl (by norm_num)).2
  have hb5 : (6539895670557897912396 : Real) / 2 ^ 40 <= Chebyshev.theta (5948091642 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0755 hb4 5941346624 le_rfl (by norm_num)).2
  have hb6 : (6547316087966555142154 : Real) / 2 ^ 40 <= Chebyshev.theta (5954848074 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0756 hb5 5948091642 le_rfl (by norm_num)).2
  have hb7 : (6554736878935124686298 : Real) / 2 ^ 40 <= Chebyshev.theta (5961596118 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0757 hb6 5954848074 le_rfl (by norm_num)).2
  have hb8 : (6562158043258004411070 : Real) / 2 ^ 40 <= Chebyshev.theta (5968342748 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0758 hb7 5961596118 le_rfl (by norm_num)).2
  have hb9 : (6569579580316527262402 : Real) / 2 ^ 40 <= Chebyshev.theta (5975091680 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0759 hb8 5968342748 le_rfl (by norm_num)).2
  have hb10 : (6577001489512679432241 : Real) / 2 ^ 40 <= Chebyshev.theta (5981827938 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0760 hb9 5975091680 le_rfl (by norm_num)).2
  have hb11 : (6584423769915390262375 : Real) / 2 ^ 40 <= Chebyshev.theta (5988573978 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0761 hb10 5981827938 le_rfl (by norm_num)).2
  have hb12 : (6591846422260547932906 : Real) / 2 ^ 40 <= Chebyshev.theta (5995331262 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0762 hb11 5988573978 le_rfl (by norm_num)).2
  have hb13 : (6599269445866409260043 : Real) / 2 ^ 40 <= Chebyshev.theta (6002084240 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0763 hb12 5995331262 le_rfl (by norm_num)).2
  have hb14 : (6606692840514719671027 : Real) / 2 ^ 40 <= Chebyshev.theta (6008833320 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0764 hb13 6002084240 le_rfl (by norm_num)).2
  have hb15 : (6614116605357207556988 : Real) / 2 ^ 40 <= Chebyshev.theta (6015583038 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0765 hb14 6008833320 le_rfl (by norm_num)).2
  have hb16 : (6621540740554633319343 : Real) / 2 ^ 40 <= Chebyshev.theta (6022340012 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0766 hb15 6015583038 le_rfl (by norm_num)).2
  have hb17 : (6628965245593456786896 : Real) / 2 ^ 40 <= Chebyshev.theta (6029099702 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0767 hb16 6022340012 le_rfl (by norm_num)).2
  have hb18 : (6636390119971487770496 : Real) / 2 ^ 40 <= Chebyshev.theta (6035850378 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0768 hb17 6029099702 le_rfl (by norm_num)).2
  have hb19 : (6643815363452423365280 : Real) / 2 ^ 40 <= Chebyshev.theta (6042611624 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0769 hb18 6035850378 le_rfl (by norm_num)).2
  have hb20 : (6651240975659853510984 : Real) / 2 ^ 40 <= Chebyshev.theta (6049373928 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0770 hb19 6042611624 le_rfl (by norm_num)).2
  have hb21 : (6658666956404921948998 : Real) / 2 ^ 40 <= Chebyshev.theta (6056127194 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0771 hb20 6049373928 le_rfl (by norm_num)).2
  have hb22 : (6666093304625381999118 : Real) / 2 ^ 40 <= Chebyshev.theta (6062871338 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0772 hb21 6056127194 le_rfl (by norm_num)).2
  have hb23 : (6673520019585903677082 : Real) / 2 ^ 40 <= Chebyshev.theta (6069621882 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0773 hb22 6062871338 le_rfl (by norm_num)).2
  have hb24 : (6680947101441479360645 : Real) / 2 ^ 40 <= Chebyshev.theta (6076374680 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0774 hb23 6069621882 le_rfl (by norm_num)).2
  have hb25 : (6688374550014974903800 : Real) / 2 ^ 40 <= Chebyshev.theta (6083136758 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0775 hb24 6076374680 le_rfl (by norm_num)).2
  have hb26 : (6695802364519892370444 : Real) / 2 ^ 40 <= Chebyshev.theta (6089886192 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0776 hb25 6083136758 le_rfl (by norm_num)).2
  have hb27 : (6703230544691832998522 : Real) / 2 ^ 40 <= Chebyshev.theta (6096643418 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0777 hb26 6089886192 le_rfl (by norm_num)).2
  have hb28 : (6710659090166667036211 : Real) / 2 ^ 40 <= Chebyshev.theta (6103398728 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0778 hb27 6096643418 le_rfl (by norm_num)).2
  have hb29 : (6718088000736745631680 : Real) / 2 ^ 40 <= Chebyshev.theta (6110161088 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0779 hb28 6103398728 le_rfl (by norm_num)).2
  have hb30 : (6725517276046311970679 : Real) / 2 ^ 40 <= Chebyshev.theta (6116919674 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0780 hb29 6110161088 le_rfl (by norm_num)).2
  have hb31 : (6732946915506097313289 : Real) / 2 ^ 40 <= Chebyshev.theta (6123671934 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0781 hb30 6116919674 le_rfl (by norm_num)).2
  have hb32 : (6740376917813830768857 : Real) / 2 ^ 40 <= Chebyshev.theta (6130408410 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0782 hb31 6123671934 le_rfl (by norm_num)).2
  have hb33 : (6747807283102362946888 : Real) / 2 ^ 40 <= Chebyshev.theta (6137161568 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0783 hb32 6130408410 le_rfl (by norm_num)).2
  have hb34 : (6755238011612834449509 : Real) / 2 ^ 40 <= Chebyshev.theta (6143914038 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0784 hb33 6137161568 le_rfl (by norm_num)).2
  have hb35 : (6762669102681736490311 : Real) / 2 ^ 40 <= Chebyshev.theta (6150678914 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0785 hb34 6143914038 le_rfl (by norm_num)).2
  have hb36 : (6770100556208965948968 : Real) / 2 ^ 40 <= Chebyshev.theta (6157444880 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0786 hb35 6150678914 le_rfl (by norm_num)).2
  have hb37 : (6777532371668516280562 : Real) / 2 ^ 40 <= Chebyshev.theta (6164195354 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0787 hb36 6157444880 le_rfl (by norm_num)).2
  have hb38 : (6784964548600434114369 : Real) / 2 ^ 40 <= Chebyshev.theta (6170962928 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0788 hb37 6164195354 le_rfl (by norm_num)).2
  have hb39 : (6792397086789814052661 : Real) / 2 ^ 40 <= Chebyshev.theta (6177720392 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0789 hb38 6170962928 le_rfl (by norm_num)).2
  have hb40 : (6799829985559564543632 : Real) / 2 ^ 40 <= Chebyshev.theta (6184479030 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0790 hb39 6177720392 le_rfl (by norm_num)).2
  have hb41 : (6807263244859075831280 : Real) / 2 ^ 40 <= Chebyshev.theta (6191237672 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0791 hb40 6184479030 le_rfl (by norm_num)).2
  have hb42 : (6814696863818492734321 : Real) / 2 ^ 40 <= Chebyshev.theta (6197991348 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0792 hb41 6191237672 le_rfl (by norm_num)).2
  have hb43 : (6822130841967070095826 : Real) / 2 ^ 40 <= Chebyshev.theta (6204751038 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0793 hb42 6197991348 le_rfl (by norm_num)).2
  have hb44 : (6829565179502781373096 : Real) / 2 ^ 40 <= Chebyshev.theta (6211506398 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0794 hb43 6204751038 le_rfl (by norm_num)).2
  have hb45 : (6836999875958788780070 : Real) / 2 ^ 40 <= Chebyshev.theta (6218283482 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0795 hb44 6211506398 le_rfl (by norm_num)).2
  have hb46 : (6844434931248013765979 : Real) / 2 ^ 40 <= Chebyshev.theta (6225039854 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0796 hb45 6218283482 le_rfl (by norm_num)).2
  have hb47 : (6851870344658942702325 : Real) / 2 ^ 40 <= Chebyshev.theta (6231802692 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0797 hb46 6225039854 le_rfl (by norm_num)).2
  have hb48 : (6859306115833027795668 : Real) / 2 ^ 40 <= Chebyshev.theta (6238561458 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0798 hb47 6231802692 le_rfl (by norm_num)).2
  have hb49 : (6866742244396091769096 : Real) / 2 ^ 40 <= Chebyshev.theta (6245334134 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0799 hb48 6238561458 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0800 hb49 6245334134 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 6083136758 with hc25 | hc25
  · rcases Nat.lt_or_ge n 5995331262 with hc12 | hc12
    · rcases Nat.lt_or_ge n 5954848074 with hc6 | hc6
      · rcases Nat.lt_or_ge n 5934592460 with hc3 | hc3
        · rcases Nat.lt_or_ge n 5921103128 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0751 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5927850158 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0752 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0753 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5941346624 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0754 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5948091642 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0755 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0756 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 5975091680 with hc9 | hc9
        · rcases Nat.lt_or_ge n 5961596118 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0757 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5968342748 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0758 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0759 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5981827938 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0760 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5988573978 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0761 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0762 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 6035850378 with hc18 | hc18
      · rcases Nat.lt_or_ge n 6015583038 with hc15 | hc15
        · rcases Nat.lt_or_ge n 6002084240 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0763 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6008833320 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0764 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0765 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6022340012 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0766 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6029099702 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0767 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0768 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 6056127194 with hc21 | hc21
        · rcases Nat.lt_or_ge n 6042611624 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0769 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6049373928 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0770 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0771 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6069621882 with hc23 | hc23
          · rcases Nat.lt_or_ge n 6062871338 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0772 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0773 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6076374680 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0774 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0775 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 6164195354 with hc37 | hc37
    · rcases Nat.lt_or_ge n 6123671934 with hc31 | hc31
      · rcases Nat.lt_or_ge n 6103398728 with hc28 | hc28
        · rcases Nat.lt_or_ge n 6089886192 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0776 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6096643418 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0777 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0778 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6110161088 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0779 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6116919674 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0780 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0781 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 6143914038 with hc34 | hc34
        · rcases Nat.lt_or_ge n 6130408410 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0782 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6137161568 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0783 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0784 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6150678914 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0785 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6157444880 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0786 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0787 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 6204751038 with hc43 | hc43
      · rcases Nat.lt_or_ge n 6184479030 with hc40 | hc40
        · rcases Nat.lt_or_ge n 6170962928 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0788 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6177720392 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0789 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0790 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6191237672 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0791 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6197991348 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0792 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0793 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 6225039854 with hc46 | hc46
        · rcases Nat.lt_or_ge n 6211506398 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0794 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6218283482 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0795 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0796 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6238561458 with hc48 | hc48
          · rcases Nat.lt_or_ge n 6231802692 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0797 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0798 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6245334134 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0799 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0800 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (6502799203779927993439 : Real) / 2 ^ 40 <= Chebyshev.theta (5914357088 : Real))
    (n : Nat) (h1 : 5914357088 <= n) (h2 : n <= 6252112019) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((6874178730578669503809 : Real) / 2 ^ 40 <= Chebyshev.theta (6252112020 : Real)) :=
  TFPLink.blk hbase n h1 h2
