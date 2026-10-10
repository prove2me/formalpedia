-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_grp02
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:27:15.427428+00:00
-- url     : https://prove2.me/submissions/ccf8f5e4-245f-4e5c-b229-384d7a8f12fc

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert052
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert053
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert054
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert055
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert056
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert057
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert058
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert059
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert060
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert061
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert062
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert063
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert064
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert065
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert066
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert067
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert068
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert069
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert070
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert071
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert072
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert073
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert074
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert075
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert076
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert077
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert078
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert079
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert080
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert081
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert082
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert083
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert084
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert085
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert086
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert087
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert088
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert089
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert090
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert091
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert092
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert093
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert094
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert095
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert096
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert097
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert098
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert099
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert100
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert101

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_grp02` (the range 393128004 <= n <= 693190903 with its carry in and carry out) from the 50 Phase 1 certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert052` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert101`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (432220832279890113048 : Real) / 2 ^ 40 <= Chebyshev.theta (393128004 : Real))
    (n : Nat) (h1 : 393128004 <= n) (h2 : n <= 693190903) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((762135668912283162940 : Real) / 2 ^ 40 <= Chebyshev.theta (693190904 : Real)) := by
  have hb0 := hbase
  have hb1 : (438720162594367374519 : Real) / 2 ^ 40 <= Chebyshev.theta (399042702 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert052 hb0 393128004 le_rfl (by norm_num)).2
  have hb2 : (445224358338395164829 : Real) / 2 ^ 40 <= Chebyshev.theta (404956580 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert053 hb1 399042702 le_rfl (by norm_num)).2
  have hb3 : (451733351471436040779 : Real) / 2 ^ 40 <= Chebyshev.theta (410875274 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert054 hb2 404956580 le_rfl (by norm_num)).2
  have hb4 : (458247076737233400394 : Real) / 2 ^ 40 <= Chebyshev.theta (416799212 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert055 hb3 410875274 le_rfl (by norm_num)).2
  have hb5 : (464765471319962846559 : Real) / 2 ^ 40 <= Chebyshev.theta (422732928 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert056 hb4 416799212 le_rfl (by norm_num)).2
  have hb6 : (471288470584453680001 : Real) / 2 ^ 40 <= Chebyshev.theta (428659842 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert057 hb5 422732928 le_rfl (by norm_num)).2
  have hb7 : (477816016178587556865 : Real) / 2 ^ 40 <= Chebyshev.theta (434599368 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert058 hb6 428659842 le_rfl (by norm_num)).2
  have hb8 : (484348049404722909416 : Real) / 2 ^ 40 <= Chebyshev.theta (440543372 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert059 hb7 434599368 le_rfl (by norm_num)).2
  have hb9 : (490884508741119358897 : Real) / 2 ^ 40 <= Chebyshev.theta (446484090 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert060 hb8 440543372 le_rfl (by norm_num)).2
  have hb10 : (497425340650655862257 : Real) / 2 ^ 40 <= Chebyshev.theta (452433602 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert061 hb9 446484090 le_rfl (by norm_num)).2
  have hb11 : (503970490490239355578 : Real) / 2 ^ 40 <= Chebyshev.theta (458385602 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert062 hb10 452433602 le_rfl (by norm_num)).2
  have hb12 : (510519906148567031997 : Real) / 2 ^ 40 <= Chebyshev.theta (464340914 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert063 hb11 458385602 le_rfl (by norm_num)).2
  have hb13 : (517073532751824881116 : Real) / 2 ^ 40 <= Chebyshev.theta (470299910 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert064 hb12 464340914 le_rfl (by norm_num)).2
  have hb14 : (523631323108648214468 : Real) / 2 ^ 40 <= Chebyshev.theta (476271710 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert065 hb13 470299910 le_rfl (by norm_num)).2
  have hb15 : (530193224740441363615 : Real) / 2 ^ 40 <= Chebyshev.theta (482231700 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert066 hb14 476271710 le_rfl (by norm_num)).2
  have hb16 : (536759189634361431455 : Real) / 2 ^ 40 <= Chebyshev.theta (488204660 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert067 hb15 482231700 le_rfl (by norm_num)).2
  have hb17 : (543329172451137520856 : Real) / 2 ^ 40 <= Chebyshev.theta (494180658 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert068 hb16 488204660 le_rfl (by norm_num)).2
  have hb18 : (549903124636662836886 : Real) / 2 ^ 40 <= Chebyshev.theta (500158950 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert069 hb17 494180658 le_rfl (by norm_num)).2
  have hb19 : (556481007097319716668 : Real) / 2 ^ 40 <= Chebyshev.theta (506149782 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert070 hb18 500158950 le_rfl (by norm_num)).2
  have hb20 : (563062775463423434123 : Real) / 2 ^ 40 <= Chebyshev.theta (512140712 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert071 hb19 506149782 le_rfl (by norm_num)).2
  have hb21 : (569648385879015499646 : Real) / 2 ^ 40 <= Chebyshev.theta (518131040 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert072 hb20 512140712 le_rfl (by norm_num)).2
  have hb22 : (576237791361682533557 : Real) / 2 ^ 40 <= Chebyshev.theta (524125040 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert073 hb21 518131040 le_rfl (by norm_num)).2
  have hb23 : (582830951760025759483 : Real) / 2 ^ 40 <= Chebyshev.theta (530117382 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert074 hb22 524125040 le_rfl (by norm_num)).2
  have hb24 : (589427826052419089208 : Real) / 2 ^ 40 <= Chebyshev.theta (536118548 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert075 hb23 530117382 le_rfl (by norm_num)).2
  have hb25 : (596028373735986433537 : Real) / 2 ^ 40 <= Chebyshev.theta (542123004 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert076 hb24 536118548 le_rfl (by norm_num)).2
  have hb26 : (602632561039693512653 : Real) / 2 ^ 40 <= Chebyshev.theta (548130750 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert077 hb25 542123004 le_rfl (by norm_num)).2
  have hb27 : (609240343544548301429 : Real) / 2 ^ 40 <= Chebyshev.theta (554131368 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert078 hb26 548130750 le_rfl (by norm_num)).2
  have hb28 : (615851686523513114393 : Real) / 2 ^ 40 <= Chebyshev.theta (560150714 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert079 hb27 554131368 le_rfl (by norm_num)).2
  have hb29 : (622466555512460505892 : Real) / 2 ^ 40 <= Chebyshev.theta (566166204 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert080 hb28 560150714 le_rfl (by norm_num)).2
  have hb30 : (629084914842862476593 : Real) / 2 ^ 40 <= Chebyshev.theta (572187692 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert081 hb29 566166204 le_rfl (by norm_num)).2
  have hb31 : (635706728842841852135 : Real) / 2 ^ 40 <= Chebyshev.theta (578210628 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert082 hb30 572187692 le_rfl (by norm_num)).2
  have hb32 : (642331962622553827553 : Real) / 2 ^ 40 <= Chebyshev.theta (584231732 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert083 hb31 578210628 le_rfl (by norm_num)).2
  have hb33 : (648960584159791684288 : Real) / 2 ^ 40 <= Chebyshev.theta (590261978 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert084 hb32 584231732 le_rfl (by norm_num)).2
  have hb34 : (655592556568974430329 : Real) / 2 ^ 40 <= Chebyshev.theta (596283782 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert085 hb33 590261978 le_rfl (by norm_num)).2
  have hb35 : (662227848773851227682 : Real) / 2 ^ 40 <= Chebyshev.theta (602321844 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert086 hb34 596283782 le_rfl (by norm_num)).2
  have hb36 : (668866429311341522443 : Real) / 2 ^ 40 <= Chebyshev.theta (608354970 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert087 hb35 602321844 le_rfl (by norm_num)).2
  have hb37 : (675508269938782616888 : Real) / 2 ^ 40 <= Chebyshev.theta (614398092 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert088 hb36 608354970 le_rfl (by norm_num)).2
  have hb38 : (682153340610911386285 : Real) / 2 ^ 40 <= Chebyshev.theta (620446704 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert089 hb37 614398092 le_rfl (by norm_num)).2
  have hb39 : (688801611561934755589 : Real) / 2 ^ 40 <= Chebyshev.theta (626495240 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert090 hb38 620446704 le_rfl (by norm_num)).2
  have hb40 : (695453050243453396043 : Real) / 2 ^ 40 <= Chebyshev.theta (632540862 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert091 hb39 626495240 le_rfl (by norm_num)).2
  have hb41 : (702107630830536850695 : Real) / 2 ^ 40 <= Chebyshev.theta (638593340 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert092 hb40 632540862 le_rfl (by norm_num)).2
  have hb42 : (708765323229731087442 : Real) / 2 ^ 40 <= Chebyshev.theta (644655242 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert093 hb41 638593340 le_rfl (by norm_num)).2
  have hb43 : (715426101088796647459 : Real) / 2 ^ 40 <= Chebyshev.theta (650706242 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert094 hb42 644655242 le_rfl (by norm_num)).2
  have hb44 : (722089935156783083852 : Real) / 2 ^ 40 <= Chebyshev.theta (656768864 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert095 hb43 650706242 le_rfl (by norm_num)).2
  have hb45 : (728756798384822531651 : Real) / 2 ^ 40 <= Chebyshev.theta (662826500 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert096 hb44 656768864 le_rfl (by norm_num)).2
  have hb46 : (735426664859975656738 : Real) / 2 ^ 40 <= Chebyshev.theta (668897498 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert097 hb45 662826500 le_rfl (by norm_num)).2
  have hb47 : (742099510508744477332 : Real) / 2 ^ 40 <= Chebyshev.theta (674966234 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert098 hb46 668897498 le_rfl (by norm_num)).2
  have hb48 : (748775310892756998710 : Real) / 2 ^ 40 <= Chebyshev.theta (681044628 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert099 hb47 674966234 le_rfl (by norm_num)).2
  have hb49 : (755454040236762193524 : Real) / 2 ^ 40 <= Chebyshev.theta (687113858 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert100 hb48 681044628 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert101 hb49 687113858 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 542123004 with hc25 | hc25
  · rcases Nat.lt_or_ge n 464340914 with hc12 | hc12
    · rcases Nat.lt_or_ge n 428659842 with hc6 | hc6
      · rcases Nat.lt_or_ge n 410875274 with hc3 | hc3
        · rcases Nat.lt_or_ge n 399042702 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert052 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 404956580 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert053 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert054 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 416799212 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert055 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 422732928 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert056 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert057 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 446484090 with hc9 | hc9
        · rcases Nat.lt_or_ge n 434599368 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert058 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 440543372 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert059 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert060 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 452433602 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert061 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 458385602 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert062 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert063 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 500158950 with hc18 | hc18
      · rcases Nat.lt_or_ge n 482231700 with hc15 | hc15
        · rcases Nat.lt_or_ge n 470299910 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert064 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 476271710 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert065 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert066 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 488204660 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert067 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 494180658 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert068 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert069 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 518131040 with hc21 | hc21
        · rcases Nat.lt_or_ge n 506149782 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert070 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 512140712 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert071 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert072 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 530117382 with hc23 | hc23
          · rcases Nat.lt_or_ge n 524125040 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert073 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert074 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 536118548 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert075 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert076 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 614398092 with hc37 | hc37
    · rcases Nat.lt_or_ge n 578210628 with hc31 | hc31
      · rcases Nat.lt_or_ge n 560150714 with hc28 | hc28
        · rcases Nat.lt_or_ge n 548130750 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert077 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 554131368 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert078 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert079 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 566166204 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert080 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 572187692 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert081 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert082 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 596283782 with hc34 | hc34
        · rcases Nat.lt_or_ge n 584231732 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert083 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 590261978 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert084 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert085 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 602321844 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert086 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 608354970 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert087 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert088 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 650706242 with hc43 | hc43
      · rcases Nat.lt_or_ge n 632540862 with hc40 | hc40
        · rcases Nat.lt_or_ge n 620446704 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert089 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 626495240 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert090 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert091 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 638593340 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert092 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 644655242 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert093 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert094 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 668897498 with hc46 | hc46
        · rcases Nat.lt_or_ge n 656768864 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert095 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 662826500 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert096 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert097 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 681044628 with hc48 | hc48
          · rcases Nat.lt_or_ge n 674966234 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert098 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert099 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 687113858 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert100 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert101 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (432220832279890113048 : Real) / 2 ^ 40 <= Chebyshev.theta (393128004 : Real))
    (n : Nat) (h1 : 393128004 <= n) (h2 : n <= 693190903) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((762135668912283162940 : Real) / 2 ^ 40 <= Chebyshev.theta (693190904 : Real)) :=
  TFPLink.blk hbase n h1 h2
