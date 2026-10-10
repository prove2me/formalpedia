-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp15
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T00:17:55.977453+00:00
-- url     : https://prove2.me/submissions/1a4fcb7d-f938-46c5-b3c7-d8bdc600afa0

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0701
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0702
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0703
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0704
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0705
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0706
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0707
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0708
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0709
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0710
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0711
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0712
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0713
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0714
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0715
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0716
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0717
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0718
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0719
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0720
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0721
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0722
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0723
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0724
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0725
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0726
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0727
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0728
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0729
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0730
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0731
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0732
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0733
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0734
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0735
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0736
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0737
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0738
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0739
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0740
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0741
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0742
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0743
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0744
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0745
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0746
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0747
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0748
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0749
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0750

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp15` (the range 5577453188 <= n <= 5914357087 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0701` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0750`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (6132360425961107643378 : Real) / 2 ^ 40 <= Chebyshev.theta (5577453188 : Real))
    (n : Nat) (h1 : 5577453188 <= n) (h2 : n <= 5914357087) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((6502799203779927993439 : Real) / 2 ^ 40 <= Chebyshev.theta (5914357088 : Real)) := by
  have hb0 := hbase
  have hb1 : (6139759642579962294894 : Real) / 2 ^ 40 <= Chebyshev.theta (5584173048 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0701 hb0 5577453188 le_rfl (by norm_num)).2
  have hb2 : (6147159256283520733571 : Real) / 2 ^ 40 <= Chebyshev.theta (5590901978 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0702 hb1 5584173048 le_rfl (by norm_num)).2
  have hb3 : (6154559266873809502107 : Real) / 2 ^ 40 <= Chebyshev.theta (5597630892 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0703 hb2 5590901978 le_rfl (by norm_num)).2
  have hb4 : (6161959673747977095185 : Real) / 2 ^ 40 <= Chebyshev.theta (5604365528 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0704 hb3 5597630892 le_rfl (by norm_num)).2
  have hb5 : (6169360476522356906644 : Real) / 2 ^ 40 <= Chebyshev.theta (5611091738 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0705 hb4 5604365528 le_rfl (by norm_num)).2
  have hb6 : (6176761674488412352456 : Real) / 2 ^ 40 <= Chebyshev.theta (5617816802 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0706 hb5 5611091738 le_rfl (by norm_num)).2
  have hb7 : (6184163267220612138589 : Real) / 2 ^ 40 <= Chebyshev.theta (5624546342 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0707 hb6 5617816802 le_rfl (by norm_num)).2
  have hb8 : (6191565254571406498465 : Real) / 2 ^ 40 <= Chebyshev.theta (5631278894 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0708 hb7 5624546342 le_rfl (by norm_num)).2
  have hb9 : (6198967636244393441969 : Real) / 2 ^ 40 <= Chebyshev.theta (5638017312 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0709 hb8 5631278894 le_rfl (by norm_num)).2
  have hb10 : (6206370411436329157849 : Real) / 2 ^ 40 <= Chebyshev.theta (5644737048 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0710 hb9 5638017312 le_rfl (by norm_num)).2
  have hb11 : (6213773579683725035073 : Real) / 2 ^ 40 <= Chebyshev.theta (5651477942 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0711 hb10 5644737048 le_rfl (by norm_num)).2
  have hb12 : (6221177141023794129525 : Real) / 2 ^ 40 <= Chebyshev.theta (5658207540 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0712 hb11 5651477942 le_rfl (by norm_num)).2
  have hb13 : (6228581094722136783338 : Real) / 2 ^ 40 <= Chebyshev.theta (5664941550 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0713 hb12 5658207540 le_rfl (by norm_num)).2
  have hb14 : (6235985439865916735683 : Real) / 2 ^ 40 <= Chebyshev.theta (5671668800 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0714 hb13 5664941550 le_rfl (by norm_num)).2
  have hb15 : (6243390176287675235083 : Real) / 2 ^ 40 <= Chebyshev.theta (5678395278 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0715 hb14 5671668800 le_rfl (by norm_num)).2
  have hb16 : (6250795303175609467433 : Real) / 2 ^ 40 <= Chebyshev.theta (5685120614 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0716 hb15 5678395278 le_rfl (by norm_num)).2
  have hb17 : (6258200820515020275659 : Real) / 2 ^ 40 <= Chebyshev.theta (5691861464 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0717 hb16 5685120614 le_rfl (by norm_num)).2
  have hb18 : (6265606728106817810782 : Real) / 2 ^ 40 <= Chebyshev.theta (5698600674 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0718 hb17 5691861464 le_rfl (by norm_num)).2
  have hb19 : (6273013025952118464479 : Real) / 2 ^ 40 <= Chebyshev.theta (5705343384 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0719 hb18 5698600674 le_rfl (by norm_num)).2
  have hb20 : (6280419712778421790804 : Real) / 2 ^ 40 <= Chebyshev.theta (5712070158 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0720 hb19 5705343384 le_rfl (by norm_num)).2
  have hb21 : (6287826788479856645768 : Real) / 2 ^ 40 <= Chebyshev.theta (5718807288 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0721 hb20 5712070158 le_rfl (by norm_num)).2
  have hb22 : (6295234252486132947951 : Real) / 2 ^ 40 <= Chebyshev.theta (5725551930 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0722 hb21 5718807288 le_rfl (by norm_num)).2
  have hb23 : (6302642104698450033982 : Real) / 2 ^ 40 <= Chebyshev.theta (5732292902 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0723 hb22 5725551930 le_rfl (by norm_num)).2
  have hb24 : (6310050344319704246830 : Real) / 2 ^ 40 <= Chebyshev.theta (5739024900 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0724 hb23 5732292902 le_rfl (by norm_num)).2
  have hb25 : (6317458970743694906149 : Real) / 2 ^ 40 <= Chebyshev.theta (5745757170 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0725 hb24 5739024900 le_rfl (by norm_num)).2
  have hb26 : (6324867983738398608503 : Real) / 2 ^ 40 <= Chebyshev.theta (5752501512 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0726 hb25 5745757170 le_rfl (by norm_num)).2
  have hb27 : (6332277383034764959852 : Real) / 2 ^ 40 <= Chebyshev.theta (5759236584 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0727 hb26 5752501512 le_rfl (by norm_num)).2
  have hb28 : (6339687168254895377696 : Real) / 2 ^ 40 <= Chebyshev.theta (5765981582 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0728 hb27 5759236584 le_rfl (by norm_num)).2
  have hb29 : (6347097339009727362770 : Real) / 2 ^ 40 <= Chebyshev.theta (5772721980 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0729 hb28 5765981582 le_rfl (by norm_num)).2
  have hb30 : (6354507894890847626750 : Real) / 2 ^ 40 <= Chebyshev.theta (5779458632 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0730 hb29 5772721980 le_rfl (by norm_num)).2
  have hb31 : (6361918835352898835659 : Real) / 2 ^ 40 <= Chebyshev.theta (5786208084 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0731 hb30 5779458632 le_rfl (by norm_num)).2
  have hb32 : (6369330160123853550986 : Real) / 2 ^ 40 <= Chebyshev.theta (5792953022 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0732 hb31 5786208084 le_rfl (by norm_num)).2
  have hb33 : (6376741868825627124952 : Real) / 2 ^ 40 <= Chebyshev.theta (5799695442 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0733 hb32 5792953022 le_rfl (by norm_num)).2
  have hb34 : (6384153960495517801843 : Real) / 2 ^ 40 <= Chebyshev.theta (5806433630 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0734 hb33 5799695442 le_rfl (by norm_num)).2
  have hb35 : (6391566434929970165975 : Real) / 2 ^ 40 <= Chebyshev.theta (5813174694 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0735 hb34 5806433630 le_rfl (by norm_num)).2
  have hb36 : (6398979291760202833539 : Real) / 2 ^ 40 <= Chebyshev.theta (5819917250 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0736 hb35 5813174694 le_rfl (by norm_num)).2
  have hb37 : (6406392530619109008243 : Real) / 2 ^ 40 <= Chebyshev.theta (5826663654 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0737 hb36 5819917250 le_rfl (by norm_num)).2
  have hb38 : (6413806151174934296882 : Real) / 2 ^ 40 <= Chebyshev.theta (5833405962 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0738 hb37 5826663654 le_rfl (by norm_num)).2
  have hb39 : (6421220152539403055510 : Real) / 2 ^ 40 <= Chebyshev.theta (5840143610 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0739 hb38 5833405962 le_rfl (by norm_num)).2
  have hb40 : (6428634534808152837748 : Real) / 2 ^ 40 <= Chebyshev.theta (5846896802 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0740 hb39 5840143610 le_rfl (by norm_num)).2
  have hb41 : (6436049297411079627457 : Real) / 2 ^ 40 <= Chebyshev.theta (5853637008 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0741 hb40 5846896802 le_rfl (by norm_num)).2
  have hb42 : (6443464440166397646644 : Real) / 2 ^ 40 <= Chebyshev.theta (5860383144 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0742 hb41 5853637008 le_rfl (by norm_num)).2
  have hb43 : (6450879962035676570872 : Real) / 2 ^ 40 <= Chebyshev.theta (5867123924 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0743 hb42 5860383144 le_rfl (by norm_num)).2
  have hb44 : (6458295862725305389218 : Real) / 2 ^ 40 <= Chebyshev.theta (5873861480 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0744 hb43 5867123924 le_rfl (by norm_num)).2
  have hb45 : (6465712141608058044761 : Real) / 2 ^ 40 <= Chebyshev.theta (5880603480 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0745 hb44 5873861480 le_rfl (by norm_num)).2
  have hb46 : (6473128799072810971487 : Real) / 2 ^ 40 <= Chebyshev.theta (5887367694 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0746 hb45 5880603480 le_rfl (by norm_num)).2
  have hb47 : (6480545834566019963124 : Real) / 2 ^ 40 <= Chebyshev.theta (5894106038 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0747 hb46 5887367694 le_rfl (by norm_num)).2
  have hb48 : (6487963247397196767748 : Real) / 2 ^ 40 <= Chebyshev.theta (5900858784 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0748 hb47 5894106038 le_rfl (by norm_num)).2
  have hb49 : (6495381037472564484533 : Real) / 2 ^ 40 <= Chebyshev.theta (5907603588 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0749 hb48 5900858784 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0750 hb49 5907603588 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 5745757170 with hc25 | hc25
  · rcases Nat.lt_or_ge n 5658207540 with hc12 | hc12
    · rcases Nat.lt_or_ge n 5617816802 with hc6 | hc6
      · rcases Nat.lt_or_ge n 5597630892 with hc3 | hc3
        · rcases Nat.lt_or_ge n 5584173048 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0701 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5590901978 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0702 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0703 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5604365528 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0704 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5611091738 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0705 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0706 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 5638017312 with hc9 | hc9
        · rcases Nat.lt_or_ge n 5624546342 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0707 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5631278894 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0708 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0709 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5644737048 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0710 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5651477942 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0711 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0712 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 5698600674 with hc18 | hc18
      · rcases Nat.lt_or_ge n 5678395278 with hc15 | hc15
        · rcases Nat.lt_or_ge n 5664941550 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0713 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5671668800 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0714 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0715 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5685120614 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0716 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5691861464 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0717 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0718 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 5718807288 with hc21 | hc21
        · rcases Nat.lt_or_ge n 5705343384 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0719 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5712070158 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0720 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0721 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5732292902 with hc23 | hc23
          · rcases Nat.lt_or_ge n 5725551930 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0722 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0723 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5739024900 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0724 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0725 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 5826663654 with hc37 | hc37
    · rcases Nat.lt_or_ge n 5786208084 with hc31 | hc31
      · rcases Nat.lt_or_ge n 5765981582 with hc28 | hc28
        · rcases Nat.lt_or_ge n 5752501512 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0726 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5759236584 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0727 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0728 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5772721980 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0729 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5779458632 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0730 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0731 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 5806433630 with hc34 | hc34
        · rcases Nat.lt_or_ge n 5792953022 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0732 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5799695442 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0733 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0734 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5813174694 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0735 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5819917250 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0736 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0737 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 5867123924 with hc43 | hc43
      · rcases Nat.lt_or_ge n 5846896802 with hc40 | hc40
        · rcases Nat.lt_or_ge n 5833405962 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0738 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5840143610 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0739 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0740 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5853637008 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0741 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5860383144 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0742 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0743 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 5887367694 with hc46 | hc46
        · rcases Nat.lt_or_ge n 5873861480 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0744 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5880603480 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0745 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0746 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5900858784 with hc48 | hc48
          · rcases Nat.lt_or_ge n 5894106038 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0747 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0748 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 5907603588 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0749 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0750 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (6132360425961107643378 : Real) / 2 ^ 40 <= Chebyshev.theta (5577453188 : Real))
    (n : Nat) (h1 : 5577453188 <= n) (h2 : n <= 5914357087) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((6502799203779927993439 : Real) / 2 ^ 40 <= Chebyshev.theta (5914357088 : Real)) :=
  TFPLink.blk hbase n h1 h2
