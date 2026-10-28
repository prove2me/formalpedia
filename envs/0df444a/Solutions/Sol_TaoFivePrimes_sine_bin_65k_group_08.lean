-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_group_08
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:50:29.915273+00:00
-- url     : https://prove2.me/submissions/03daa0e9-6f06-4d92-a837-2d61228fa071

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+96))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+96)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+96):ℝ)/10000 := by
  fin_cases i
  ·
    have hx : |x - (407393395/9244998:ℝ)| ≤ (170495981/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (407393395/9244998:ℝ) - (14:ℝ)*Real.pi := by linarith
    have hd : (84061219/1000000000:ℝ) ≤ |(407393395/9244998:ℝ) - (14:ℝ)*Real.pi| ∧
        |(407393395/9244998:ℝ) - (14:ℝ)*Real.pi| ≤ (4203061/50000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (407393395/9244998:ℝ) (84061219/1000000000:ℝ) (4203061/50000000:ℝ) (170495981/1000000000:ℝ)
      14 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((4203061/50000000:ℝ) - (84061219/1000000000:ℝ)^3/6 + (4203061/50000000:ℝ)^5/100)^2 + (170495981/1000000000:ℝ) ≤ (1776/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (410166895/9244998:ℝ)| ≤ (42658879/250000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (410166895/9244998:ℝ) - (14:ℝ)*Real.pi := by linarith
    have hd : (96015321/250000000:ℝ) ≤ |(410166895/9244998:ℝ) - (14:ℝ)*Real.pi| ∧
        |(410166895/9244998:ℝ) - (14:ℝ)*Real.pi| ≤ (76812257/200000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (410166895/9244998:ℝ) (96015321/250000000:ℝ) (76812257/200000000:ℝ) (42658879/250000000:ℝ)
      14 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((76812257/200000000:ℝ) - (96015321/250000000:ℝ)^3/6 + (76812257/200000000:ℝ)^5/100)^2 + (42658879/250000000:ℝ) ≤ (3111/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (58991485/1320714:ℝ)| ≤ (170775051/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (58991485/1320714:ℝ) - (14:ℝ)*Real.pi := by linarith
    have hd : (684061349/1000000000:ℝ) ≤ |(58991485/1320714:ℝ) - (14:ℝ)*Real.pi| ∧
        |(58991485/1320714:ℝ) - (14:ℝ)*Real.pi| ≤ (13681227/20000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (58991485/1320714:ℝ) (684061349/1000000000:ℝ) (13681227/20000000:ℝ) (170775051/1000000000:ℝ)
      14 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((13681227/20000000:ℝ) - (684061349/1000000000:ℝ)^3/6 + (13681227/20000000:ℝ)^5/100)^2 + (170775051/1000000000:ℝ) ≤ (5705/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (415713895/9244998:ℝ)| ≤ (85457293/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (415713895/9244998:ℝ) - (14:ℝ)*Real.pi := by linarith
    have hd : (492030707/500000000:ℝ) ≤ |(415713895/9244998:ℝ) - (14:ℝ)*Real.pi| ∧
        |(415713895/9244998:ℝ) - (14:ℝ)*Real.pi| ≤ (196812283/200000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (415713895/9244998:ℝ) (492030707/500000000:ℝ) (196812283/200000000:ℝ) (85457293/500000000:ℝ)
      14 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((196812283/200000000:ℝ) - (492030707/500000000:ℝ)^3/6 + (196812283/200000000:ℝ)^5/100)^2 + (85457293/500000000:ℝ) ≤ (8673/10000:ℝ) := by norm_num
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
    have hx : |x - (426807895/9244998:ℝ)| ≤ (85736363/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (426807895/9244998:ℝ) - (15:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (957530979/1000000000:ℝ) ≤ |(426807895/9244998:ℝ) - (15:ℝ)*Real.pi| ∧
        |(426807895/9244998:ℝ) - (15:ℝ)*Real.pi| ≤ (47876549/50000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (426807895/9244998:ℝ) (957530979/1000000000:ℝ) (47876549/50000000:ℝ) (85736363/500000000:ℝ)
      15 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((47876549/50000000:ℝ) - (957530979/1000000000:ℝ)^3/6 + (47876549/50000000:ℝ)^5/100)^2 + (85736363/500000000:ℝ) ≤ (8427/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (429581395/9244998:ℝ)| ≤ (8580613/50000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (429581395/9244998:ℝ) - (15:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (328765457/500000000:ℝ) ≤ |(429581395/9244998:ℝ) - (15:ℝ)*Real.pi| ∧
        |(429581395/9244998:ℝ) - (15:ℝ)*Real.pi| ≤ (131506183/200000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (429581395/9244998:ℝ) (328765457/500000000:ℝ) (131506183/200000000:ℝ) (8580613/50000000:ℝ)
      15 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((131506183/200000000:ℝ) - (328765457/500000000:ℝ)^3/6 + (131506183/200000000:ℝ)^5/100)^2 + (8580613/50000000:ℝ) ≤ (5454/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (61764985/1320714:ℝ)| ≤ (34350359/200000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (61764985/1320714:ℝ) - (15:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (357530849/1000000000:ℝ) ≤ |(61764985/1320714:ℝ) - (15:ℝ)*Real.pi| ∧
        |(61764985/1320714:ℝ) - (15:ℝ)*Real.pi| ≤ (7150617/20000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (61764985/1320714:ℝ) (357530849/1000000000:ℝ) (7150617/20000000:ℝ) (34350359/200000000:ℝ)
      15 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((7150617/20000000:ℝ) - (357530849/1000000000:ℝ)^3/6 + (7150617/20000000:ℝ)^5/100)^2 + (34350359/200000000:ℝ) ≤ (2943/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (435128395/9244998:ℝ)| ≤ (17189133/100000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (435128395/9244998:ℝ) - (15:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (1797837/31250000:ℝ) ≤ |(435128395/9244998:ℝ) - (15:ℝ)*Real.pi| ∧
        |(435128395/9244998:ℝ) - (15:ℝ)*Real.pi| ≤ (11506157/200000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (435128395/9244998:ℝ) (1797837/31250000:ℝ) (11506157/200000000:ℝ) (17189133/100000000:ℝ)
      15 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((11506157/200000000:ℝ) - (1797837/31250000:ℝ)^3/6 + (11506157/200000000:ℝ)^5/100)^2 + (17189133/100000000:ℝ) ≤ (1752/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (437901895/9244998:ℝ)| ≤ (34406173/200000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (437901895/9244998:ℝ) - (15:ℝ)*Real.pi := by linarith
    have hd : (1515433/6250000:ℝ) ≤ |(437901895/9244998:ℝ) - (15:ℝ)*Real.pi| ∧
        |(437901895/9244998:ℝ) - (15:ℝ)*Real.pi| ≤ (242469281/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (437901895/9244998:ℝ) (1515433/6250000:ℝ) (242469281/1000000000:ℝ) (34406173/200000000:ℝ)
      15 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((242469281/1000000000:ℝ) - (1515433/6250000:ℝ)^3/6 + (242469281/1000000000:ℝ)^5/100)^2 + (34406173/200000000:ℝ) ≤ (2297/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
