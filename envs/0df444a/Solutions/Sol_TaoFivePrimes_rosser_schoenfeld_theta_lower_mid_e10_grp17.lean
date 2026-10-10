-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp17
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T00:23:48.103475+00:00
-- url     : https://prove2.me/submissions/a5863563-9184-48aa-9285-942d581a9198

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0801
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0802
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0803
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0804
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0805
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0806
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0807
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0808
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0809
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0810
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0811
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0812
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0813
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0814
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0815
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0816
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0817
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0818
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0819
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0820
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0821
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0822
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0823
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0824
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0825
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0826
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0827
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0828
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0829
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0830
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0831
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0832
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0833
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0834
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0835
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0836
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0837
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0838
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0839
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0840
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0841
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0842
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0843
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0844
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0845
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0846
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0847
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0848
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0849
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0850

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp17` (the range 6252112020 <= n <= 6590693513 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0801` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0850`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (6874178730578669503809 : Real) / 2 ^ 40 <= Chebyshev.theta (6252112020 : Real))
    (n : Nat) (h1 : 6252112020 <= n) (h2 : n <= 6590693513) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((7246450329781067871514 : Real) / 2 ^ 40 <= Chebyshev.theta (6590693514 : Real)) := by
  have hb0 := hbase
  have hb1 : (6881615573386800277152 : Real) / 2 ^ 40 <= Chebyshev.theta (6258863922 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0801 hb0 6252112020 le_rfl (by norm_num)).2
  have hb2 : (6889052772408163429932 : Real) / 2 ^ 40 <= Chebyshev.theta (6265631168 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0802 hb1 6258863922 le_rfl (by norm_num)).2
  have hb3 : (6896490327827335719332 : Real) / 2 ^ 40 <= Chebyshev.theta (6272400104 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0803 hb2 6265631168 le_rfl (by norm_num)).2
  have hb4 : (6903928238416100235908 : Real) / 2 ^ 40 <= Chebyshev.theta (6279156600 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0804 hb3 6272400104 le_rfl (by norm_num)).2
  have hb5 : (6911366503657381568155 : Real) / 2 ^ 40 <= Chebyshev.theta (6285908090 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0805 hb4 6279156600 le_rfl (by norm_num)).2
  have hb6 : (6918805123396559468876 : Real) / 2 ^ 40 <= Chebyshev.theta (6292673592 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0806 hb5 6285908090 le_rfl (by norm_num)).2
  have hb7 : (6926244097593629902995 : Real) / 2 ^ 40 <= Chebyshev.theta (6299431452 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0807 hb6 6292673592 le_rfl (by norm_num)).2
  have hb8 : (6933683425844831214174 : Real) / 2 ^ 40 <= Chebyshev.theta (6306204042 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0808 hb7 6299431452 le_rfl (by norm_num)).2
  have hb9 : (6941123107857296652607 : Real) / 2 ^ 40 <= Chebyshev.theta (6312967100 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0809 hb8 6306204042 le_rfl (by norm_num)).2
  have hb10 : (6948563143490732997612 : Real) / 2 ^ 40 <= Chebyshev.theta (6319737872 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0810 hb9 6312967100 le_rfl (by norm_num)).2
  have hb11 : (6956003531996227499528 : Real) / 2 ^ 40 <= Chebyshev.theta (6326508998 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0811 hb10 6319737872 le_rfl (by norm_num)).2
  have hb12 : (6963444273484675064889 : Real) / 2 ^ 40 <= Chebyshev.theta (6333280244 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0812 hb11 6326508998 le_rfl (by norm_num)).2
  have hb13 : (6970885367265215311212 : Real) / 2 ^ 40 <= Chebyshev.theta (6340049342 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0813 hb12 6333280244 le_rfl (by norm_num)).2
  have hb14 : (6978326813359245745630 : Real) / 2 ^ 40 <= Chebyshev.theta (6346819650 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0814 hb13 6340049342 le_rfl (by norm_num)).2
  have hb15 : (6985768611020086401835 : Real) / 2 ^ 40 <= Chebyshev.theta (6353594180 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0815 hb14 6346819650 le_rfl (by norm_num)).2
  have hb16 : (6993210760313976519301 : Real) / 2 ^ 40 <= Chebyshev.theta (6360369230 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0816 hb15 6353594180 le_rfl (by norm_num)).2
  have hb17 : (7000653260462418968938 : Real) / 2 ^ 40 <= Chebyshev.theta (6367137182 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0817 hb16 6360369230 le_rfl (by norm_num)).2
  have hb18 : (7008096110987784178478 : Real) / 2 ^ 40 <= Chebyshev.theta (6373901154 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0818 hb17 6367137182 le_rfl (by norm_num)).2
  have hb19 : (7015539311567434953408 : Real) / 2 ^ 40 <= Chebyshev.theta (6380666078 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0819 hb18 6373901154 le_rfl (by norm_num)).2
  have hb20 : (7022982861820681732038 : Real) / 2 ^ 40 <= Chebyshev.theta (6387438648 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0820 hb19 6380666078 le_rfl (by norm_num)).2
  have hb21 : (7030426761795157225898 : Real) / 2 ^ 40 <= Chebyshev.theta (6394212984 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0821 hb20 6387438648 le_rfl (by norm_num)).2
  have hb22 : (7037871011143105427755 : Real) / 2 ^ 40 <= Chebyshev.theta (6400992864 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0822 hb21 6394212984 le_rfl (by norm_num)).2
  have hb23 : (7045315609430249975445 : Real) / 2 ^ 40 <= Chebyshev.theta (6407761100 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0823 hb22 6400992864 le_rfl (by norm_num)).2
  have hb24 : (7052760555911771555453 : Real) / 2 ^ 40 <= Chebyshev.theta (6414527258 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0824 hb23 6407761100 le_rfl (by norm_num)).2
  have hb25 : (7060205850882025439821 : Real) / 2 ^ 40 <= Chebyshev.theta (6421316684 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0825 hb24 6414527258 le_rfl (by norm_num)).2
  have hb26 : (7067651493802724775189 : Real) / 2 ^ 40 <= Chebyshev.theta (6428089752 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0826 hb25 6421316684 le_rfl (by norm_num)).2
  have hb27 : (7075097484076600014623 : Real) / 2 ^ 40 <= Chebyshev.theta (6434864660 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0827 hb26 6428089752 le_rfl (by norm_num)).2
  have hb28 : (7082543821645784856223 : Real) / 2 ^ 40 <= Chebyshev.theta (6441641268 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0828 hb27 6434864660 le_rfl (by norm_num)).2
  have hb29 : (7089990505874122109656 : Real) / 2 ^ 40 <= Chebyshev.theta (6448409324 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0829 hb28 6441641268 le_rfl (by norm_num)).2
  have hb30 : (7097437536307612493140 : Real) / 2 ^ 40 <= Chebyshev.theta (6455190438 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0830 hb29 6448409324 le_rfl (by norm_num)).2
  have hb31 : (7104884913206561332582 : Real) / 2 ^ 40 <= Chebyshev.theta (6461963060 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0831 hb30 6455190438 le_rfl (by norm_num)).2
  have hb32 : (7112332635524909627089 : Real) / 2 ^ 40 <= Chebyshev.theta (6468741564 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0832 hb31 6461963060 le_rfl (by norm_num)).2
  have hb33 : (7119780703491889800904 : Real) / 2 ^ 40 <= Chebyshev.theta (6475515902 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0833 hb32 6468741564 le_rfl (by norm_num)).2
  have hb34 : (7127229115988319198323 : Real) / 2 ^ 40 <= Chebyshev.theta (6482281428 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0834 hb33 6475515902 le_rfl (by norm_num)).2
  have hb35 : (7134677872978287220418 : Real) / 2 ^ 40 <= Chebyshev.theta (6489063672 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0835 hb34 6482281428 le_rfl (by norm_num)).2
  have hb36 : (7142126974458258626880 : Real) / 2 ^ 40 <= Chebyshev.theta (6495834872 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0836 hb35 6489063672 le_rfl (by norm_num)).2
  have hb37 : (7149576419533817619542 : Real) / 2 ^ 40 <= Chebyshev.theta (6502612778 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0837 hb36 6495834872 le_rfl (by norm_num)).2
  have hb38 : (7157026208024666942647 : Real) / 2 ^ 40 <= Chebyshev.theta (6509378700 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0838 hb37 6502612778 le_rfl (by norm_num)).2
  have hb39 : (7164476339317721500510 : Real) / 2 ^ 40 <= Chebyshev.theta (6516147558 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0839 hb38 6509378700 le_rfl (by norm_num)).2
  have hb40 : (7171926813023732728586 : Real) / 2 ^ 40 <= Chebyshev.theta (6522917928 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0840 hb39 6516147558 le_rfl (by norm_num)).2
  have hb41 : (7179377629096556437579 : Real) / 2 ^ 40 <= Chebyshev.theta (6529691028 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0841 hb40 6522917928 le_rfl (by norm_num)).2
  have hb42 : (7186828787129826057239 : Real) / 2 ^ 40 <= Chebyshev.theta (6536464184 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0842 hb41 6529691028 le_rfl (by norm_num)).2
  have hb43 : (7194280286767412642757 : Real) / 2 ^ 40 <= Chebyshev.theta (6543246210 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0843 hb42 6536464184 le_rfl (by norm_num)).2
  have hb44 : (7201732128165797094125 : Real) / 2 ^ 40 <= Chebyshev.theta (6550022184 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0844 hb43 6543246210 le_rfl (by norm_num)).2
  have hb45 : (7209184310849768687707 : Real) / 2 ^ 40 <= Chebyshev.theta (6556807974 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0845 hb44 6550022184 le_rfl (by norm_num)).2
  have hb46 : (7216636834566278643493 : Real) / 2 ^ 40 <= Chebyshev.theta (6563584244 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0846 hb45 6556807974 le_rfl (by norm_num)).2
  have hb47 : (7224089698746339337020 : Real) / 2 ^ 40 <= Chebyshev.theta (6570359282 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0847 hb46 6563584244 le_rfl (by norm_num)).2
  have hb48 : (7231542902876782727651 : Real) / 2 ^ 40 <= Chebyshev.theta (6577135892 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0848 hb47 6570359282 le_rfl (by norm_num)).2
  have hb49 : (7238996446575802862017 : Real) / 2 ^ 40 <= Chebyshev.theta (6583911470 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0849 hb48 6577135892 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0850 hb49 6583911470 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 6421316684 with hc25 | hc25
  · rcases Nat.lt_or_ge n 6333280244 with hc12 | hc12
    · rcases Nat.lt_or_ge n 6292673592 with hc6 | hc6
      · rcases Nat.lt_or_ge n 6272400104 with hc3 | hc3
        · rcases Nat.lt_or_ge n 6258863922 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0801 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6265631168 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0802 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0803 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6279156600 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0804 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6285908090 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0805 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0806 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 6312967100 with hc9 | hc9
        · rcases Nat.lt_or_ge n 6299431452 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0807 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6306204042 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0808 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0809 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6319737872 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0810 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6326508998 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0811 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0812 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 6373901154 with hc18 | hc18
      · rcases Nat.lt_or_ge n 6353594180 with hc15 | hc15
        · rcases Nat.lt_or_ge n 6340049342 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0813 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6346819650 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0814 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0815 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6360369230 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0816 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6367137182 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0817 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0818 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 6394212984 with hc21 | hc21
        · rcases Nat.lt_or_ge n 6380666078 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0819 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6387438648 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0820 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0821 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6407761100 with hc23 | hc23
          · rcases Nat.lt_or_ge n 6400992864 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0822 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0823 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6414527258 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0824 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0825 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 6502612778 with hc37 | hc37
    · rcases Nat.lt_or_ge n 6461963060 with hc31 | hc31
      · rcases Nat.lt_or_ge n 6441641268 with hc28 | hc28
        · rcases Nat.lt_or_ge n 6428089752 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0826 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6434864660 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0827 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0828 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6448409324 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0829 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6455190438 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0830 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0831 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 6482281428 with hc34 | hc34
        · rcases Nat.lt_or_ge n 6468741564 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0832 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6475515902 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0833 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0834 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6489063672 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0835 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6495834872 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0836 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0837 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 6543246210 with hc43 | hc43
      · rcases Nat.lt_or_ge n 6522917928 with hc40 | hc40
        · rcases Nat.lt_or_ge n 6509378700 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0838 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6516147558 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0839 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0840 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6529691028 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0841 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6536464184 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0842 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0843 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 6563584244 with hc46 | hc46
        · rcases Nat.lt_or_ge n 6550022184 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0844 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6556807974 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0845 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0846 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6577135892 with hc48 | hc48
          · rcases Nat.lt_or_ge n 6570359282 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0847 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0848 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6583911470 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0849 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0850 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (6874178730578669503809 : Real) / 2 ^ 40 <= Chebyshev.theta (6252112020 : Real))
    (n : Nat) (h1 : 6252112020 <= n) (h2 : n <= 6590693513) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((7246450329781067871514 : Real) / 2 ^ 40 <= Chebyshev.theta (6590693514 : Real)) :=
  TFPLink.blk hbase n h1 h2
