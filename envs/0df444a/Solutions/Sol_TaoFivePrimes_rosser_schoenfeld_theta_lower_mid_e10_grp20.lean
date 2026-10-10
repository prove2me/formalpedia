-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp20
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T00:34:27.726973+00:00
-- url     : https://prove2.me/submissions/73af6348-2669-43e7-8b29-8f8ecd1a3283

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0951
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0952
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0953
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0954
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0955
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0956
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0957
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0958
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0959
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0960
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0961
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0962
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0963
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0964
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0965
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0966
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0967
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0968
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0969
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0970
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0971
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0972
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0973
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0974
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0975
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0976
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0977
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0978
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0979
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0980
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0981
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0982
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0983
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0984
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0985
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0986
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0987
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0988
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0989
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0990
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0991
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0992
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0993
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0994
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0995
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0996
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0997
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0998
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0999
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg1000

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp20` (the range 7270138658 <= n <= 7610969533 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0951` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1000`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (7993498298181659601707 : Real) / 2 ^ 40 <= Chebyshev.theta (7270138658 : Real))
    (n : Nat) (h1 : 7270138658 <= n) (h2 : n <= 7610969533) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((8368198731656839134845 : Real) / 2 ^ 40 <= Chebyshev.theta (7610969534 : Real)) := by
  have hb0 := hbase
  have hb1 : (8000984854176102486592 : Real) / 2 ^ 40 <= Chebyshev.theta (7276951268 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0951 hb0 7270138658 le_rfl (by norm_num)).2
  have hb2 : (8008471718773580118473 : Real) / 2 ^ 40 <= Chebyshev.theta (7283766594 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0952 hb1 7276951268 le_rfl (by norm_num)).2
  have hb3 : (8015958891935949115070 : Real) / 2 ^ 40 <= Chebyshev.theta (7290579372 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0953 hb2 7283766594 le_rfl (by norm_num)).2
  have hb4 : (8023446373137016866186 : Real) / 2 ^ 40 <= Chebyshev.theta (7297392192 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0954 hb3 7290579372 le_rfl (by norm_num)).2
  have hb5 : (8030934162268121248641 : Real) / 2 ^ 40 <= Chebyshev.theta (7304206220 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0955 hb4 7297392192 le_rfl (by norm_num)).2
  have hb6 : (8038422258784090993737 : Real) / 2 ^ 40 <= Chebyshev.theta (7311016160 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0956 hb5 7304206220 le_rfl (by norm_num)).2
  have hb7 : (8045910662665947442973 : Real) / 2 ^ 40 <= Chebyshev.theta (7317834614 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0957 hb6 7311016160 le_rfl (by norm_num)).2
  have hb8 : (8053399373162358998056 : Real) / 2 ^ 40 <= Chebyshev.theta (7324633608 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0958 hb7 7317834614 le_rfl (by norm_num)).2
  have hb9 : (8060888389939338482428 : Real) / 2 ^ 40 <= Chebyshev.theta (7331435198 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0959 hb8 7324633608 le_rfl (by norm_num)).2
  have hb10 : (8068377712592193913354 : Real) / 2 ^ 40 <= Chebyshev.theta (7338247122 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0960 hb9 7331435198 le_rfl (by norm_num)).2
  have hb11 : (8075867341193118619248 : Real) / 2 ^ 40 <= Chebyshev.theta (7345052258 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0961 hb10 7338247122 le_rfl (by norm_num)).2
  have hb12 : (8083357275514182632821 : Real) / 2 ^ 40 <= Chebyshev.theta (7351865072 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0962 hb11 7345052258 le_rfl (by norm_num)).2
  have hb13 : (8090847515584226072384 : Real) / 2 ^ 40 <= Chebyshev.theta (7358686484 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0963 hb12 7351865072 le_rfl (by norm_num)).2
  have hb14 : (8098338060965065204905 : Real) / 2 ^ 40 <= Chebyshev.theta (7365496560 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0964 hb13 7358686484 le_rfl (by norm_num)).2
  have hb15 : (8105828911376671784858 : Real) / 2 ^ 40 <= Chebyshev.theta (7372317984 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0965 hb14 7365496560 le_rfl (by norm_num)).2
  have hb16 : (8113320066979248017824 : Real) / 2 ^ 40 <= Chebyshev.theta (7379141604 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0966 hb15 7372317984 le_rfl (by norm_num)).2
  have hb17 : (8120811527165290766499 : Real) / 2 ^ 40 <= Chebyshev.theta (7385955404 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0967 hb16 7379141604 le_rfl (by norm_num)).2
  have hb18 : (8128303291443029497379 : Real) / 2 ^ 40 <= Chebyshev.theta (7392760290 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0968 hb17 7385955404 le_rfl (by norm_num)).2
  have hb19 : (8135795359110439911216 : Real) / 2 ^ 40 <= Chebyshev.theta (7399569510 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0969 hb18 7392760290 le_rfl (by norm_num)).2
  have hb20 : (8143287730310048012046 : Real) / 2 ^ 40 <= Chebyshev.theta (7406383782 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0970 hb19 7399569510 le_rfl (by norm_num)).2
  have hb21 : (8150780404640324926882 : Real) / 2 ^ 40 <= Chebyshev.theta (7413188052 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0971 hb20 7406383782 le_rfl (by norm_num)).2
  have hb22 : (8158273381692299171561 : Real) / 2 ^ 40 <= Chebyshev.theta (7419992018 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0972 hb21 7413188052 le_rfl (by norm_num)).2
  have hb23 : (8165766661570539433117 : Real) / 2 ^ 40 <= Chebyshev.theta (7426814028 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0973 hb22 7419992018 le_rfl (by norm_num)).2
  have hb24 : (8173260244042650177556 : Real) / 2 ^ 40 <= Chebyshev.theta (7433632232 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0974 hb23 7426814028 le_rfl (by norm_num)).2
  have hb25 : (8180754128800879432718 : Real) / 2 ^ 40 <= Chebyshev.theta (7440447692 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0975 hb24 7433632232 le_rfl (by norm_num)).2
  have hb26 : (8188248315575246478167 : Real) / 2 ^ 40 <= Chebyshev.theta (7447257068 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0976 hb25 7440447692 le_rfl (by norm_num)).2
  have hb27 : (8195742803825231677191 : Real) / 2 ^ 40 <= Chebyshev.theta (7454069180 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0977 hb26 7447257068 le_rfl (by norm_num)).2
  have hb28 : (8203237593626005402675 : Real) / 2 ^ 40 <= Chebyshev.theta (7460889210 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0978 hb27 7454069180 le_rfl (by norm_num)).2
  have hb29 : (8210732684847880154864 : Real) / 2 ^ 40 <= Chebyshev.theta (7467708248 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0979 hb28 7460889210 le_rfl (by norm_num)).2
  have hb30 : (8218228077064766443888 : Real) / 2 ^ 40 <= Chebyshev.theta (7474538060 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0980 hb29 7467708248 le_rfl (by norm_num)).2
  have hb31 : (8225723770301224886631 : Real) / 2 ^ 40 <= Chebyshev.theta (7481352588 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0981 hb30 7474538060 le_rfl (by norm_num)).2
  have hb32 : (8233219763905468809289 : Real) / 2 ^ 40 <= Chebyshev.theta (7488170004 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0982 hb31 7481352588 le_rfl (by norm_num)).2
  have hb33 : (8240716057500157825199 : Real) / 2 ^ 40 <= Chebyshev.theta (7494978654 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0983 hb32 7488170004 le_rfl (by norm_num)).2
  have hb34 : (8248212650891225847928 : Real) / 2 ^ 40 <= Chebyshev.theta (7501801194 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0984 hb33 7494978654 le_rfl (by norm_num)).2
  have hb35 : (8255709543992524653105 : Real) / 2 ^ 40 <= Chebyshev.theta (7508617020 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0985 hb34 7501801194 le_rfl (by norm_num)).2
  have hb36 : (8263206736336286128270 : Real) / 2 ^ 40 <= Chebyshev.theta (7515434412 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0986 hb35 7508617020 le_rfl (by norm_num)).2
  have hb37 : (8270704227818499782229 : Real) / 2 ^ 40 <= Chebyshev.theta (7522252040 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0987 hb36 7515434412 le_rfl (by norm_num)).2
  have hb38 : (8278202018372926375508 : Real) / 2 ^ 40 <= Chebyshev.theta (7529074434 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0988 hb37 7522252040 le_rfl (by norm_num)).2
  have hb39 : (8285700107532728122045 : Real) / 2 ^ 40 <= Chebyshev.theta (7535897808 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0989 hb38 7529074434 le_rfl (by norm_num)).2
  have hb40 : (8293198495194266661204 : Real) / 2 ^ 40 <= Chebyshev.theta (7542725120 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0990 hb39 7535897808 le_rfl (by norm_num)).2
  have hb41 : (8300697181244228237818 : Real) / 2 ^ 40 <= Chebyshev.theta (7549547810 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0991 hb40 7542725120 le_rfl (by norm_num)).2
  have hb42 : (8308196165259128275930 : Real) / 2 ^ 40 <= Chebyshev.theta (7556362764 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0992 hb41 7549547810 le_rfl (by norm_num)).2
  have hb43 : (8315695446647465252268 : Real) / 2 ^ 40 <= Chebyshev.theta (7563184998 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0993 hb42 7556362764 le_rfl (by norm_num)).2
  have hb44 : (8323195025219452581824 : Real) / 2 ^ 40 <= Chebyshev.theta (7570001360 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0994 hb43 7563184998 le_rfl (by norm_num)).2
  have hb45 : (8330694900850426527387 : Real) / 2 ^ 40 <= Chebyshev.theta (7576829390 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0995 hb44 7570001360 le_rfl (by norm_num)).2
  have hb46 : (8338195073900981600471 : Real) / 2 ^ 40 <= Chebyshev.theta (7583667098 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0996 hb45 7576829390 le_rfl (by norm_num)).2
  have hb47 : (8345695543689560682564 : Real) / 2 ^ 40 <= Chebyshev.theta (7590485562 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0997 hb46 7583667098 le_rfl (by norm_num)).2
  have hb48 : (8353196310157739275929 : Real) / 2 ^ 40 <= Chebyshev.theta (7597318524 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0998 hb47 7590485562 le_rfl (by norm_num)).2
  have hb49 : (8360697372901755724227 : Real) / 2 ^ 40 <= Chebyshev.theta (7604144568 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0999 hb48 7597318524 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1000 hb49 7604144568 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 7440447692 with hc25 | hc25
  · rcases Nat.lt_or_ge n 7351865072 with hc12 | hc12
    · rcases Nat.lt_or_ge n 7311016160 with hc6 | hc6
      · rcases Nat.lt_or_ge n 7290579372 with hc3 | hc3
        · rcases Nat.lt_or_ge n 7276951268 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0951 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7283766594 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0952 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0953 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7297392192 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0954 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7304206220 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0955 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0956 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 7331435198 with hc9 | hc9
        · rcases Nat.lt_or_ge n 7317834614 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0957 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7324633608 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0958 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0959 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7338247122 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0960 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7345052258 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0961 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0962 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 7392760290 with hc18 | hc18
      · rcases Nat.lt_or_ge n 7372317984 with hc15 | hc15
        · rcases Nat.lt_or_ge n 7358686484 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0963 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7365496560 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0964 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0965 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7379141604 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0966 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7385955404 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0967 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0968 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 7413188052 with hc21 | hc21
        · rcases Nat.lt_or_ge n 7399569510 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0969 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7406383782 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0970 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0971 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7426814028 with hc23 | hc23
          · rcases Nat.lt_or_ge n 7419992018 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0972 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0973 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7433632232 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0974 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0975 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 7522252040 with hc37 | hc37
    · rcases Nat.lt_or_ge n 7481352588 with hc31 | hc31
      · rcases Nat.lt_or_ge n 7460889210 with hc28 | hc28
        · rcases Nat.lt_or_ge n 7447257068 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0976 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7454069180 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0977 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0978 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7467708248 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0979 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7474538060 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0980 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0981 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 7501801194 with hc34 | hc34
        · rcases Nat.lt_or_ge n 7488170004 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0982 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7494978654 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0983 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0984 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7508617020 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0985 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7515434412 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0986 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0987 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 7563184998 with hc43 | hc43
      · rcases Nat.lt_or_ge n 7542725120 with hc40 | hc40
        · rcases Nat.lt_or_ge n 7529074434 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0988 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7535897808 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0989 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0990 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7549547810 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0991 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7556362764 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0992 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0993 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 7583667098 with hc46 | hc46
        · rcases Nat.lt_or_ge n 7570001360 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0994 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7576829390 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0995 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0996 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7597318524 with hc48 | hc48
          · rcases Nat.lt_or_ge n 7590485562 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0997 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0998 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 7604144568 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0999 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1000 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (7993498298181659601707 : Real) / 2 ^ 40 <= Chebyshev.theta (7270138658 : Real))
    (n : Nat) (h1 : 7270138658 <= n) (h2 : n <= 7610969533) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((8368198731656839134845 : Real) / 2 ^ 40 <= Chebyshev.theta (7610969534 : Real)) :=
  TFPLink.blk hbase n h1 h2
