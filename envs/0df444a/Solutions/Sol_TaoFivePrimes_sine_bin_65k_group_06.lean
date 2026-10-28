-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_group_06
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:50:27.051699+00:00
-- url     : https://prove2.me/submissions/b6890e87-3c70-458b-ba92-4a3a6ec557ae

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+72))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+72)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+72):ℝ)/10000 := by
  fin_cases i
  ·
    have hx : |x - (340829395/9244998:ℝ)| ≤ (167147143/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (340829395/9244998:ℝ) - (12:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (83275503/100000000:ℝ) ≤ |(340829395/9244998:ℝ) - (12:ℝ)*Real.pi| ∧
        |(340829395/9244998:ℝ) - (12:ℝ)*Real.pi| ≤ (832755031/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (340829395/9244998:ℝ) (83275503/100000000:ℝ) (832755031/1000000000:ℝ) (167147143/1000000000:ℝ)
      12 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((832755031/1000000000:ℝ) - (83275503/100000000:ℝ)^3/6 + (832755031/1000000000:ℝ)^5/100)^2 + (167147143/1000000000:ℝ) ≤ (7156/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (343602895/9244998:ℝ)| ≤ (83643339/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (343602895/9244998:ℝ) - (12:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (106550993/200000000:ℝ) ≤ |(343602895/9244998:ℝ) - (12:ℝ)*Real.pi| ∧
        |(343602895/9244998:ℝ) - (12:ℝ)*Real.pi| ≤ (266377483/500000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (343602895/9244998:ℝ) (106550993/200000000:ℝ) (266377483/500000000:ℝ) (83643339/500000000:ℝ)
      12 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((266377483/500000000:ℝ) - (106550993/200000000:ℝ)^3/6 + (266377483/500000000:ℝ)^5/100)^2 + (83643339/500000000:ℝ) ≤ (4254/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (346376395/9244998:ℝ)| ≤ (167426213/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (346376395/9244998:ℝ) - (12:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (2327549/10000000:ℝ) ≤ |(346376395/9244998:ℝ) - (12:ℝ)*Real.pi| ∧
        |(346376395/9244998:ℝ) - (12:ℝ)*Real.pi| ≤ (232754901/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (346376395/9244998:ℝ) (2327549/10000000:ℝ) (232754901/1000000000:ℝ) (167426213/1000000000:ℝ)
      12 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((232754901/1000000000:ℝ) - (2327549/10000000:ℝ)^3/6 + (232754901/1000000000:ℝ)^5/100)^2 + (167426213/1000000000:ℝ) ≤ (2207/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (349149895/9244998:ℝ)| ≤ (41891437/250000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (349149895/9244998:ℝ) - (12:ℝ)*Real.pi := by linarith
    have hd : (16811291/250000000:ℝ) ≤ |(349149895/9244998:ℝ) - (12:ℝ)*Real.pi| ∧
        |(349149895/9244998:ℝ) - (12:ℝ)*Real.pi| ≤ (13449033/200000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (349149895/9244998:ℝ) (16811291/250000000:ℝ) (13449033/200000000:ℝ) (41891437/250000000:ℝ)
      12 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((13449033/200000000:ℝ) - (16811291/250000000:ℝ)^3/6 + (13449033/200000000:ℝ)^5/100)^2 + (41891437/250000000:ℝ) ≤ (1721/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (351923395/9244998:ℝ)| ≤ (167705283/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (351923395/9244998:ℝ) - (12:ℝ)*Real.pi := by linarith
    have hd : (367245229/1000000000:ℝ) ≤ |(351923395/9244998:ℝ) - (12:ℝ)*Real.pi| ∧
        |(351923395/9244998:ℝ) - (12:ℝ)*Real.pi| ≤ (36724523/100000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (351923395/9244998:ℝ) (367245229/1000000000:ℝ) (36724523/100000000:ℝ) (167705283/1000000000:ℝ)
      12 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((36724523/100000000:ℝ) - (367245229/1000000000:ℝ)^3/6 + (36724523/100000000:ℝ)^5/100)^2 + (167705283/1000000000:ℝ) ≤ (2967/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (50670985/1320714:ℝ)| ≤ (83922409/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (50670985/1320714:ℝ) - (12:ℝ)*Real.pi := by linarith
    have hd : (333622647/500000000:ℝ) ≤ |(50670985/1320714:ℝ) - (12:ℝ)*Real.pi| ∧
        |(50670985/1320714:ℝ) - (12:ℝ)*Real.pi| ≤ (133449059/200000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (50670985/1320714:ℝ) (333622647/500000000:ℝ) (133449059/200000000:ℝ) (83922409/500000000:ℝ)
      12 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((133449059/200000000:ℝ) - (333622647/500000000:ℝ)^3/6 + (133449059/200000000:ℝ)^5/100)^2 + (83922409/500000000:ℝ) ≤ (5511/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (357470395/9244998:ℝ)| ≤ (167984353/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (357470395/9244998:ℝ) - (12:ℝ)*Real.pi := by linarith
    have hd : (483622679/500000000:ℝ) ≤ |(357470395/9244998:ℝ) - (12:ℝ)*Real.pi| ∧
        |(357470395/9244998:ℝ) - (12:ℝ)*Real.pi| ≤ (967245359/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (357470395/9244998:ℝ) (483622679/500000000:ℝ) (967245359/1000000000:ℝ) (167984353/1000000000:ℝ)
      12 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((967245359/1000000000:ℝ) - (483622679/500000000:ℝ)^3/6 + (967245359/1000000000:ℝ)^5/100)^2 + (167984353/1000000000:ℝ) ≤ (8485/10000:ℝ) := by norm_num
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
    have hx : |x - (368564395/9244998:ℝ)| ≤ (42135623/250000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (368564395/9244998:ℝ) - (13:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (194869407/200000000:ℝ) ≤ |(368564395/9244998:ℝ) - (13:ℝ)*Real.pi| ∧
        |(368564395/9244998:ℝ) - (13:ℝ)*Real.pi| ≤ (243586759/250000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (368564395/9244998:ℝ) (194869407/200000000:ℝ) (243586759/250000000:ℝ) (42135623/250000000:ℝ)
      13 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((243586759/250000000:ℝ) - (194869407/200000000:ℝ)^3/6 + (243586759/250000000:ℝ)^5/100)^2 + (42135623/250000000:ℝ) ≤ (8558/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (371337895/9244998:ℝ)| ≤ (168682027/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (371337895/9244998:ℝ) - (13:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (67434697/100000000:ℝ) ≤ |(371337895/9244998:ℝ) - (13:ℝ)*Real.pi| ∧
        |(371337895/9244998:ℝ) - (13:ℝ)*Real.pi| ≤ (674346971/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (371337895/9244998:ℝ) (67434697/100000000:ℝ) (674346971/1000000000:ℝ) (168682027/1000000000:ℝ)
      13 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((674346971/1000000000:ℝ) - (67434697/100000000:ℝ)^3/6 + (674346971/1000000000:ℝ)^5/100)^2 + (168682027/1000000000:ℝ) ≤ (5589/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
