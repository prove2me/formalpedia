-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_group_10
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:51:06.616718+00:00
-- url     : https://prove2.me/submissions/8ebbd33b-2cb6-4fbd-9faf-4b48c36cc72b

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+120))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+120)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+120):ℝ)/10000 := by
  fin_cases i
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
    have hx : |x - (485051395/9244998:ℝ)| ≤ (174402959/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (485051395/9244998:ℝ) - (17:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (940714923/1000000000:ℝ) ≤ |(485051395/9244998:ℝ) - (17:ℝ)*Real.pi| ∧
        |(485051395/9244998:ℝ) - (17:ℝ)*Real.pi| ≤ (235178731/250000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (485051395/9244998:ℝ) (940714923/1000000000:ℝ) (235178731/250000000:ℝ) (174402959/1000000000:ℝ)
      17 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((235178731/250000000:ℝ) - (940714923/1000000000:ℝ)^3/6 + (235178731/250000000:ℝ)^5/100)^2 + (174402959/1000000000:ℝ) ≤ (8295/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (487824895/9244998:ℝ)| ≤ (87271247/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (487824895/9244998:ℝ) - (17:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (320357429/500000000:ℝ) ≤ |(487824895/9244998:ℝ) - (17:ℝ)*Real.pi| ∧
        |(487824895/9244998:ℝ) - (17:ℝ)*Real.pi| ≤ (640714859/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (487824895/9244998:ℝ) (320357429/500000000:ℝ) (640714859/1000000000:ℝ) (87271247/500000000:ℝ)
      17 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((640714859/1000000000:ℝ) - (320357429/500000000:ℝ)^3/6 + (640714859/1000000000:ℝ)^5/100)^2 + (87271247/500000000:ℝ) ≤ (5321/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (70085485/1320714:ℝ)| ≤ (174682029/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (70085485/1320714:ℝ) - (17:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (340714793/1000000000:ℝ) ≤ |(70085485/1320714:ℝ) - (17:ℝ)*Real.pi| ∧
        |(70085485/1320714:ℝ) - (17:ℝ)*Real.pi| ≤ (170357397/500000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (70085485/1320714:ℝ) (340714793/1000000000:ℝ) (170357397/500000000:ℝ) (174682029/1000000000:ℝ)
      17 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((170357397/500000000:ℝ) - (340714793/1000000000:ℝ)^3/6 + (170357397/500000000:ℝ)^5/100)^2 + (174682029/1000000000:ℝ) ≤ (2864/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (493371895/9244998:ℝ)| ≤ (174821563/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (493371895/9244998:ℝ) - (17:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (5089341/125000000:ℝ) ≤ |(493371895/9244998:ℝ) - (17:ℝ)*Real.pi| ∧
        |(493371895/9244998:ℝ) - (17:ℝ)*Real.pi| ≤ (40714729/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (493371895/9244998:ℝ) (5089341/125000000:ℝ) (40714729/1000000000:ℝ) (174821563/1000000000:ℝ)
      17 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((40714729/1000000000:ℝ) - (5089341/125000000:ℝ)^3/6 + (40714729/1000000000:ℝ)^5/100)^2 + (174821563/1000000000:ℝ) ≤ (1765/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (496145395/9244998:ℝ)| ≤ (87480549/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (496145395/9244998:ℝ) - (17:ℝ)*Real.pi := by linarith
    have hd : (51857067/200000000:ℝ) ≤ |(496145395/9244998:ℝ) - (17:ℝ)*Real.pi| ∧
        |(496145395/9244998:ℝ) - (17:ℝ)*Real.pi| ≤ (32410667/125000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (496145395/9244998:ℝ) (51857067/200000000:ℝ) (32410667/125000000:ℝ) (87480549/500000000:ℝ)
      17 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((32410667/125000000:ℝ) - (51857067/200000000:ℝ)^3/6 + (32410667/125000000:ℝ)^5/100)^2 + (87480549/500000000:ℝ) ≤ (2407/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (498918895/9244998:ℝ)| ≤ (175100633/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (498918895/9244998:ℝ) - (17:ℝ)*Real.pi := by linarith
    have hd : (2796427/5000000:ℝ) ≤ |(498918895/9244998:ℝ) - (17:ℝ)*Real.pi| ∧
        |(498918895/9244998:ℝ) - (17:ℝ)*Real.pi| ≤ (559285401/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (498918895/9244998:ℝ) (2796427/5000000:ℝ) (559285401/1000000000:ℝ) (175100633/1000000000:ℝ)
      17 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((559285401/1000000000:ℝ) - (2796427/5000000:ℝ)^3/6 + (559285401/1000000000:ℝ)^5/100)^2 + (175100633/1000000000:ℝ) ≤ (4568/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (501692395/9244998:ℝ)| ≤ (21905021/125000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (501692395/9244998:ℝ) - (17:ℝ)*Real.pi := by linarith
    have hd : (171857093/200000000:ℝ) ≤ |(501692395/9244998:ℝ) - (17:ℝ)*Real.pi| ∧
        |(501692395/9244998:ℝ) - (17:ℝ)*Real.pi| ≤ (429642733/500000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (501692395/9244998:ℝ) (171857093/200000000:ℝ) (429642733/500000000:ℝ) (21905021/125000000:ℝ)
      17 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((429642733/500000000:ℝ) - (171857093/200000000:ℝ)^3/6 + (429642733/500000000:ℝ)^5/100)^2 + (21905021/125000000:ℝ) ≤ (7502/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have h := Real.sin_sq_le_one x
    simpa [TaoFivePrimes.sineBinNumerator65k] using h
