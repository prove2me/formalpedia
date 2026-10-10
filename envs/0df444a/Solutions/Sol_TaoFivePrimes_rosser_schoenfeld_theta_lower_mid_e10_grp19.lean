-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp19
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T00:30:53.481929+00:00
-- url     : https://prove2.me/submissions/2baf4919-dc59-47bf-ae0b-a988d6a5bc2b

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0901
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0902
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0903
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0904
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0905
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0906
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0907
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0908
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0909
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0910
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0911
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0912
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0913
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0914
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0915
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0916
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0917
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0918
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0919
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0920
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0921
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0922
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0923
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0924
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0925
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0926
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0927
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0928
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0929
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0930
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0931
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0932
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0933
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0934
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0935
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0936
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0937
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0938
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0939
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0940
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0941
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0942
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0943
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0944
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0945
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0946
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0947
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0948
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0949
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0950

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp19` (the range 6930050750 <= n <= 7270138657 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0901` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0950`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (7619570092620144083607 : Real) / 2 ^ 40 <= Chebyshev.theta (6930050750 : Real))
    (n : Nat) (h1 : 6930050750 <= n) (h2 : n <= 7270138657) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((7993498298181659601707 : Real) / 2 ^ 40 <= Chebyshev.theta (7270138658 : Real)) := by
  have hb0 := hbase
  have hb1 : (7627040860642757486152 : Real) / 2 ^ 40 <= Chebyshev.theta (6936844662 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0901 hb0 6930050750 le_rfl (by norm_num)).2
  have hb2 : (7634511951545008460230 : Real) / 2 ^ 40 <= Chebyshev.theta (6943630724 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0902 hb1 6936844662 le_rfl (by norm_num)).2
  have hb3 : (7641983364980071325004 : Real) / 2 ^ 40 <= Chebyshev.theta (6950434962 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0903 hb2 6943630724 le_rfl (by norm_num)).2
  have hb4 : (7649455101153362148953 : Real) / 2 ^ 40 <= Chebyshev.theta (6957241574 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0904 hb3 6950434962 le_rfl (by norm_num)).2
  have hb5 : (7656927159512267052202 : Real) / 2 ^ 40 <= Chebyshev.theta (6964031720 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0905 hb4 6957241574 le_rfl (by norm_num)).2
  have hb6 : (7664399539423791954168 : Real) / 2 ^ 40 <= Chebyshev.theta (6970825428 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0906 hb5 6964031720 le_rfl (by norm_num)).2
  have hb7 : (7671872240842909057232 : Real) / 2 ^ 40 <= Chebyshev.theta (6977628902 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0907 hb6 6970825428 le_rfl (by norm_num)).2
  have hb8 : (7679345263401209108144 : Real) / 2 ^ 40 <= Chebyshev.theta (6984424244 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0908 hb7 6977628902 le_rfl (by norm_num)).2
  have hb9 : (7686818606894392430102 : Real) / 2 ^ 40 <= Chebyshev.theta (6991218260 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0909 hb8 6984424244 le_rfl (by norm_num)).2
  have hb10 : (7694292270506934903413 : Real) / 2 ^ 40 <= Chebyshev.theta (6998002244 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0910 hb9 6991218260 le_rfl (by norm_num)).2
  have hb11 : (7701766254440531290967 : Real) / 2 ^ 40 <= Chebyshev.theta (7004812598 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0911 hb10 6998002244 le_rfl (by norm_num)).2
  have hb12 : (7709240558515814663405 : Real) / 2 ^ 40 <= Chebyshev.theta (7011610158 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0912 hb11 7004812598 le_rfl (by norm_num)).2
  have hb13 : (7716715182176821965822 : Real) / 2 ^ 40 <= Chebyshev.theta (7018405578 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0913 hb12 7011610158 le_rfl (by norm_num)).2
  have hb14 : (7724190125049748051866 : Real) / 2 ^ 40 <= Chebyshev.theta (7025200070 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0914 hb13 7018405578 le_rfl (by norm_num)).2
  have hb15 : (7731665386793163133803 : Real) / 2 ^ 40 <= Chebyshev.theta (7031995910 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0915 hb14 7025200070 le_rfl (by norm_num)).2
  have hb16 : (7739140967376552505808 : Real) / 2 ^ 40 <= Chebyshev.theta (7038801954 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0916 hb15 7031995910 le_rfl (by norm_num)).2
  have hb17 : (7746616866423320042338 : Real) / 2 ^ 40 <= Chebyshev.theta (7045599642 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0917 hb16 7038801954 le_rfl (by norm_num)).2
  have hb18 : (7754093083410064112386 : Real) / 2 ^ 40 <= Chebyshev.theta (7052393210 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0918 hb17 7045599642 le_rfl (by norm_num)).2
  have hb19 : (7761569618187374296580 : Real) / 2 ^ 40 <= Chebyshev.theta (7059182682 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0919 hb18 7052393210 le_rfl (by norm_num)).2
  have hb20 : (7769046470028107482950 : Real) / 2 ^ 40 <= Chebyshev.theta (7065980150 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0920 hb19 7059182682 le_rfl (by norm_num)).2
  have hb21 : (7776523639314069624864 : Real) / 2 ^ 40 <= Chebyshev.theta (7072783020 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0921 hb20 7065980150 le_rfl (by norm_num)).2
  have hb22 : (7784001125544745120685 : Real) / 2 ^ 40 <= Chebyshev.theta (7079579030 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0922 hb21 7072783020 le_rfl (by norm_num)).2
  have hb23 : (7791478928493320394801 : Real) / 2 ^ 40 <= Chebyshev.theta (7086378798 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0923 hb22 7079579030 le_rfl (by norm_num)).2
  have hb24 : (7798957047773151796580 : Real) / 2 ^ 40 <= Chebyshev.theta (7093183100 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0924 hb23 7086378798 le_rfl (by norm_num)).2
  have hb25 : (7806435483152960183704 : Real) / 2 ^ 40 <= Chebyshev.theta (7099980144 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0925 hb24 7093183100 le_rfl (by norm_num)).2
  have hb26 : (7813914234560924358317 : Real) / 2 ^ 40 <= Chebyshev.theta (7106791058 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0926 hb25 7099980144 le_rfl (by norm_num)).2
  have hb27 : (7821393301551417976211 : Real) / 2 ^ 40 <= Chebyshev.theta (7113591414 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0927 hb26 7106791058 le_rfl (by norm_num)).2
  have hb28 : (7828872684112160728944 : Real) / 2 ^ 40 <= Chebyshev.theta (7120402284 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0928 hb27 7113591414 le_rfl (by norm_num)).2
  have hb29 : (7836352381521963593488 : Real) / 2 ^ 40 <= Chebyshev.theta (7127197824 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0929 hb28 7120402284 le_rfl (by norm_num)).2
  have hb30 : (7843832393297801104472 : Real) / 2 ^ 40 <= Chebyshev.theta (7133992934 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0930 hb29 7127197824 le_rfl (by norm_num)).2
  have hb31 : (7851312719498842020751 : Real) / 2 ^ 40 <= Chebyshev.theta (7140796782 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0931 hb30 7133992934 le_rfl (by norm_num)).2
  have hb32 : (7858793359972512813202 : Real) / 2 ^ 40 <= Chebyshev.theta (7147612502 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0932 hb31 7140796782 le_rfl (by norm_num)).2
  have hb33 : (7866274314764771605841 : Real) / 2 ^ 40 <= Chebyshev.theta (7154423832 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0933 hb32 7147612502 le_rfl (by norm_num)).2
  have hb34 : (7873755582973387858765 : Real) / 2 ^ 40 <= Chebyshev.theta (7161222870 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0934 hb33 7154423832 le_rfl (by norm_num)).2
  have hb35 : (7881237164503840410030 : Real) / 2 ^ 40 <= Chebyshev.theta (7168026512 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0935 hb34 7161222870 le_rfl (by norm_num)).2
  have hb36 : (7888719058985859353592 : Real) / 2 ^ 40 <= Chebyshev.theta (7174837232 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0936 hb35 7168026512 le_rfl (by norm_num)).2
  have hb37 : (7896201266494615062336 : Real) / 2 ^ 40 <= Chebyshev.theta (7181647814 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0937 hb36 7174837232 le_rfl (by norm_num)).2
  have hb38 : (7903683786503914926066 : Real) / 2 ^ 40 <= Chebyshev.theta (7188456660 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0938 hb37 7181647814 le_rfl (by norm_num)).2
  have hb39 : (7911166618792341262272 : Real) / 2 ^ 40 <= Chebyshev.theta (7195258914 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0939 hb38 7188456660 le_rfl (by norm_num)).2
  have hb40 : (7918649763102193658960 : Real) / 2 ^ 40 <= Chebyshev.theta (7202068904 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0940 hb39 7195258914 le_rfl (by norm_num)).2
  have hb41 : (7926133219030826851467 : Real) / 2 ^ 40 <= Chebyshev.theta (7208880662 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0941 hb40 7202068904 le_rfl (by norm_num)).2
  have hb42 : (7933616986296351941474 : Real) / 2 ^ 40 <= Chebyshev.theta (7215693384 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0942 hb41 7208880662 le_rfl (by norm_num)).2
  have hb43 : (7941101064808899399021 : Real) / 2 ^ 40 <= Chebyshev.theta (7222493154 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0943 hb42 7215693384 le_rfl (by norm_num)).2
  have hb44 : (7948585453654702636881 : Real) / 2 ^ 40 <= Chebyshev.theta (7229296448 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0944 hb43 7222493154 le_rfl (by norm_num)).2
  have hb45 : (7956070153196775015201 : Real) / 2 ^ 40 <= Chebyshev.theta (7236110472 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0945 hb44 7229296448 le_rfl (by norm_num)).2
  have hb46 : (7963555163116572775616 : Real) / 2 ^ 40 <= Chebyshev.theta (7242923240 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0946 hb45 7236110472 le_rfl (by norm_num)).2
  have hb47 : (7971040482901300008047 : Real) / 2 ^ 40 <= Chebyshev.theta (7249726260 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0947 hb46 7242923240 le_rfl (by norm_num)).2
  have hb48 : (7978526112155754059008 : Real) / 2 ^ 40 <= Chebyshev.theta (7256533968 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0948 hb47 7249726260 le_rfl (by norm_num)).2
  have hb49 : (7986012050842907937895 : Real) / 2 ^ 40 <= Chebyshev.theta (7263338462 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0949 hb48 7256533968 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0950 hb49 7263338462 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 7099980144 with hc25 | hc25
  · rcases Nat.lt_or_ge n 7011610158 with hc12 | hc12
    · rcases Nat.lt_or_ge n 6970825428 with hc6 | hc6
      · rcases Nat.lt_or_ge n 6950434962 with hc3 | hc3
        · rcases Nat.lt_or_ge n 6936844662 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0901 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6943630724 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0902 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0903 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6957241574 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0904 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6964031720 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0905 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0906 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 6991218260 with hc9 | hc9
        · rcases Nat.lt_or_ge n 6977628902 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0907 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 6984424244 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0908 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0909 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 6998002244 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0910 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7004812598 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0911 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0912 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 7052393210 with hc18 | hc18
      · rcases Nat.lt_or_ge n 7031995910 with hc15 | hc15
        · rcases Nat.lt_or_ge n 7018405578 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0913 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7025200070 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0914 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0915 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7038801954 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0916 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7045599642 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0917 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0918 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 7072783020 with hc21 | hc21
        · rcases Nat.lt_or_ge n 7059182682 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0919 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7065980150 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0920 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0921 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7086378798 with hc23 | hc23
          · rcases Nat.lt_or_ge n 7079579030 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0922 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0923 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7093183100 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0924 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0925 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 7181647814 with hc37 | hc37
    · rcases Nat.lt_or_ge n 7140796782 with hc31 | hc31
      · rcases Nat.lt_or_ge n 7120402284 with hc28 | hc28
        · rcases Nat.lt_or_ge n 7106791058 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0926 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7113591414 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0927 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0928 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7127197824 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0929 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7133992934 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0930 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0931 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 7161222870 with hc34 | hc34
        · rcases Nat.lt_or_ge n 7147612502 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0932 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7154423832 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0933 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0934 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7168026512 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0935 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7174837232 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0936 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0937 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 7222493154 with hc43 | hc43
      · rcases Nat.lt_or_ge n 7202068904 with hc40 | hc40
        · rcases Nat.lt_or_ge n 7188456660 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0938 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7195258914 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0939 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0940 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7208880662 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0941 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7215693384 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0942 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0943 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 7242923240 with hc46 | hc46
        · rcases Nat.lt_or_ge n 7229296448 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0944 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7236110472 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0945 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0946 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7256533968 with hc48 | hc48
          · rcases Nat.lt_or_ge n 7249726260 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0947 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0948 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7263338462 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0949 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0950 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (7619570092620144083607 : Real) / 2 ^ 40 <= Chebyshev.theta (6930050750 : Real))
    (n : Nat) (h1 : 6930050750 <= n) (h2 : n <= 7270138657) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((7993498298181659601707 : Real) / 2 ^ 40 <= Chebyshev.theta (7270138658 : Real)) :=
  TFPLink.blk hbase n h1 h2
