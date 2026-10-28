-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_group_02
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:49:58.006516+00:00
-- url     : https://prove2.me/submissions/7db6ba0c-0c80-43b2-a5e9-895006a18100

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+24))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+24)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+24):ℝ)/10000 := by
  fin_cases i
  ·
    have hx : |x - (207701395/9244998:ℝ)| ≤ (160449467/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (207701395/9244998:ℝ) - (7:ℝ)*Real.pi := by linarith
    have hd : (237602561/500000000:ℝ) ≤ |(207701395/9244998:ℝ) - (7:ℝ)*Real.pi| ∧
        |(207701395/9244998:ℝ) - (7:ℝ)*Real.pi| ≤ (475205123/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (207701395/9244998:ℝ) (237602561/500000000:ℝ) (475205123/1000000000:ℝ) (160449467/1000000000:ℝ)
      7 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((475205123/1000000000:ℝ) - (237602561/500000000:ℝ)^3/6 + (475205123/1000000000:ℝ)^5/100)^2 + (160449467/1000000000:ℝ) ≤ (3699/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (210474895/9244998:ℝ)| ≤ (80294501/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (210474895/9244998:ℝ) - (7:ℝ)*Real.pi := by linarith
    have hd : (775205187/1000000000:ℝ) ≤ |(210474895/9244998:ℝ) - (7:ℝ)*Real.pi| ∧
        |(210474895/9244998:ℝ) - (7:ℝ)*Real.pi| ≤ (193801297/250000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (210474895/9244998:ℝ) (775205187/1000000000:ℝ) (193801297/250000000:ℝ) (80294501/500000000:ℝ)
      7 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((193801297/250000000:ℝ) - (775205187/1000000000:ℝ)^3/6 + (193801297/250000000:ℝ)^5/100)^2 + (80294501/500000000:ℝ) ≤ (6511/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have h := Real.sin_sq_le_one x
    simpa [TaoFivePrimes.sineBinNumerator65k] using h
  ·
    have h := Real.sin_sq_le_one x
    simpa [TaoFivePrimes.sineBinNumerator65k] using h
  ·
    have h := Real.sin_sq_le_one x
    simpa [TaoFivePrimes.sineBinNumerator65k] using h
  ·
    have h := Real.sin_sq_le_one x
    simpa [TaoFivePrimes.sineBinNumerator65k] using h
  ·
    have hx : |x - (224342395/9244998:ℝ)| ≤ (161286677/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (224342395/9244998:ℝ) - (8:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (866387141/1000000000:ℝ) ≤ |(224342395/9244998:ℝ) - (8:ℝ)*Real.pi| ∧
        |(224342395/9244998:ℝ) - (8:ℝ)*Real.pi| ≤ (433193571/500000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (224342395/9244998:ℝ) (866387141/1000000000:ℝ) (433193571/500000000:ℝ) (161286677/1000000000:ℝ)
      8 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((433193571/500000000:ℝ) - (866387141/1000000000:ℝ)^3/6 + (433193571/500000000:ℝ)^5/100)^2 + (161286677/1000000000:ℝ) ≤ (7433/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (227115895/9244998:ℝ)| ≤ (40356553/250000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (227115895/9244998:ℝ) - (8:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (141596769/250000000:ℝ) ≤ |(227115895/9244998:ℝ) - (8:ℝ)*Real.pi| ∧
        |(227115895/9244998:ℝ) - (8:ℝ)*Real.pi| ≤ (566387077/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (227115895/9244998:ℝ) (141596769/250000000:ℝ) (566387077/1000000000:ℝ) (40356553/250000000:ℝ)
      8 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((566387077/1000000000:ℝ) - (141596769/250000000:ℝ)^3/6 + (566387077/1000000000:ℝ)^5/100)^2 + (40356553/250000000:ℝ) ≤ (4495/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (229889395/9244998:ℝ)| ≤ (161565747/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (229889395/9244998:ℝ) - (8:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (66596753/250000000:ℝ) ≤ |(229889395/9244998:ℝ) - (8:ℝ)*Real.pi| ∧
        |(229889395/9244998:ℝ) - (8:ℝ)*Real.pi| ≤ (266387013/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (229889395/9244998:ℝ) (66596753/250000000:ℝ) (266387013/1000000000:ℝ) (161565747/1000000000:ℝ)
      8 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((266387013/1000000000:ℝ) - (66596753/250000000:ℝ)^3/6 + (266387013/1000000000:ℝ)^5/100)^2 + (161565747/1000000000:ℝ) ≤ (2309/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (232662895/9244998:ℝ)| ≤ (80852641/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (232662895/9244998:ℝ) - (8:ℝ)*Real.pi := by linarith
    have hd : (8403263/250000000:ℝ) ≤ |(232662895/9244998:ℝ) - (8:ℝ)*Real.pi| ∧
        |(232662895/9244998:ℝ) - (8:ℝ)*Real.pi| ≤ (33613053/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (232662895/9244998:ℝ) (8403263/250000000:ℝ) (33613053/1000000000:ℝ) (80852641/500000000:ℝ)
      8 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((33613053/1000000000:ℝ) - (8403263/250000000:ℝ)^3/6 + (33613053/1000000000:ℝ)^5/100)^2 + (80852641/500000000:ℝ) ≤ (1629/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (235436395/9244998:ℝ)| ≤ (10115301/62500000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (235436395/9244998:ℝ) - (8:ℝ)*Real.pi := by linarith
    have hd : (333613117/1000000000:ℝ) ≤ |(235436395/9244998:ℝ) - (8:ℝ)*Real.pi| ∧
        |(235436395/9244998:ℝ) - (8:ℝ)*Real.pi| ≤ (166806559/500000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (235436395/9244998:ℝ) (333613117/1000000000:ℝ) (166806559/500000000:ℝ) (10115301/62500000:ℝ)
      8 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((166806559/500000000:ℝ) - (333613117/1000000000:ℝ)^3/6 + (166806559/500000000:ℝ)^5/100)^2 + (10115301/62500000:ℝ) ≤ (2691/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (34029985/1320714:ℝ)| ≤ (161984351/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (34029985/1320714:ℝ) - (8:ℝ)*Real.pi := by linarith
    have hd : (316806591/500000000:ℝ) ≤ |(34029985/1320714:ℝ) - (8:ℝ)*Real.pi| ∧
        |(34029985/1320714:ℝ) - (8:ℝ)*Real.pi| ≤ (633613183/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (34029985/1320714:ℝ) (316806591/500000000:ℝ) (633613183/1000000000:ℝ) (161984351/1000000000:ℝ)
      8 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((633613183/1000000000:ℝ) - (316806591/500000000:ℝ)^3/6 + (633613183/1000000000:ℝ)^5/100)^2 + (161984351/1000000000:ℝ) ≤ (5128/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
