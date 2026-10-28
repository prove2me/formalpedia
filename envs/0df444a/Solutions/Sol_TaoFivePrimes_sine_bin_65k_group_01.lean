-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_group_01
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:49:01.185521+00:00
-- url     : https://prove2.me/submissions/b60e14c0-a3c3-428d-8d5a-11adc707c8c4

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+12))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+12)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+12):ℝ)/10000 := by
  fin_cases i
  ·
    have hx : |x - (174419395/9244998:ℝ)| ≤ (19846881/125000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (174419395/9244998:ℝ) - (6:ℝ)*Real.pi := by linarith
    have hd : (16796997/1000000000:ℝ) ≤ |(174419395/9244998:ℝ) - (6:ℝ)*Real.pi| ∧
        |(174419395/9244998:ℝ) - (6:ℝ)*Real.pi| ≤ (8398499/500000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (174419395/9244998:ℝ) (16796997/1000000000:ℝ) (8398499/500000000:ℝ) (19846881/125000000:ℝ)
      6 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((8398499/500000000:ℝ) - (16796997/1000000000:ℝ)^3/6 + (8398499/500000000:ℝ)^5/100)^2 + (19846881/125000000:ℝ) ≤ (1591/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (177192895/9244998:ℝ)| ≤ (158914583/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (177192895/9244998:ℝ) - (6:ℝ)*Real.pi := by linarith
    have hd : (316797061/1000000000:ℝ) ≤ |(177192895/9244998:ℝ) - (6:ℝ)*Real.pi| ∧
        |(177192895/9244998:ℝ) - (6:ℝ)*Real.pi| ≤ (158398531/500000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (177192895/9244998:ℝ) (316797061/1000000000:ℝ) (158398531/500000000:ℝ) (158914583/1000000000:ℝ)
      6 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((158398531/500000000:ℝ) - (316797061/1000000000:ℝ)^3/6 + (158398531/500000000:ℝ)^5/100)^2 + (158914583/1000000000:ℝ) ≤ (2560/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (25709485/1320714:ℝ)| ≤ (79527059/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (25709485/1320714:ℝ) - (6:ℝ)*Real.pi := by linarith
    have hd : (308398563/500000000:ℝ) ≤ |(25709485/1320714:ℝ) - (6:ℝ)*Real.pi| ∧
        |(25709485/1320714:ℝ) - (6:ℝ)*Real.pi| ≤ (616797127/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (25709485/1320714:ℝ) (308398563/500000000:ℝ) (616797127/1000000000:ℝ) (79527059/500000000:ℝ)
      6 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((616797127/1000000000:ℝ) - (308398563/500000000:ℝ)^3/6 + (616797127/1000000000:ℝ)^5/100)^2 + (79527059/500000000:ℝ) ≤ (4939/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (182739895/9244998:ℝ)| ≤ (159193653/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (182739895/9244998:ℝ) - (6:ℝ)*Real.pi := by linarith
    have hd : (916797191/1000000000:ℝ) ≤ |(182739895/9244998:ℝ) - (6:ℝ)*Real.pi| ∧
        |(182739895/9244998:ℝ) - (6:ℝ)*Real.pi| ≤ (114599649/125000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (182739895/9244998:ℝ) (916797191/1000000000:ℝ) (114599649/125000000:ℝ) (159193653/1000000000:ℝ)
      6 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((114599649/125000000:ℝ) - (916797191/1000000000:ℝ)^3/6 + (114599649/125000000:ℝ)^5/100)^2 + (159193653/1000000000:ℝ) ≤ (7910/10000:ℝ) := by norm_num
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
    have hx : |x - (196607395/9244998:ℝ)| ≤ (1249151/7812500:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (196607395/9244998:ℝ) - (7:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (724795137/1000000000:ℝ) ≤ |(196607395/9244998:ℝ) - (7:ℝ)*Real.pi| ∧
        |(196607395/9244998:ℝ) - (7:ℝ)*Real.pi| ≤ (362397569/500000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (196607395/9244998:ℝ) (724795137/1000000000:ℝ) (362397569/500000000:ℝ) (1249151/7812500:ℝ)
      7 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((362397569/500000000:ℝ) - (724795137/1000000000:ℝ)^3/6 + (362397569/500000000:ℝ)^5/100)^2 + (1249151/7812500:ℝ) ≤ (6000/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (28482985/1320714:ℝ)| ≤ (160030863/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (28482985/1320714:ℝ) - (7:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (6637423/15625000:ℝ) ≤ |(28482985/1320714:ℝ) - (7:ℝ)*Real.pi| ∧
        |(28482985/1320714:ℝ) - (7:ℝ)*Real.pi| ≤ (424795073/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (28482985/1320714:ℝ) (6637423/15625000:ℝ) (424795073/1000000000:ℝ) (160030863/1000000000:ℝ)
      7 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((424795073/1000000000:ℝ) - (6637423/15625000:ℝ)^3/6 + (424795073/1000000000:ℝ)^5/100)^2 + (160030863/1000000000:ℝ) ≤ (3300/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (202154395/9244998:ℝ)| ≤ (80085199/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (202154395/9244998:ℝ) - (7:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (124795007/1000000000:ℝ) ≤ |(202154395/9244998:ℝ) - (7:ℝ)*Real.pi| ∧
        |(202154395/9244998:ℝ) - (7:ℝ)*Real.pi| ≤ (974961/7812500:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (202154395/9244998:ℝ) (124795007/1000000000:ℝ) (974961/7812500:ℝ) (80085199/500000000:ℝ)
      7 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((974961/7812500:ℝ) - (124795007/1000000000:ℝ)^3/6 + (974961/7812500:ℝ)^5/100)^2 + (80085199/500000000:ℝ) ≤ (1757/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (204927895/9244998:ℝ)| ≤ (40077483/250000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (204927895/9244998:ℝ) - (7:ℝ)*Real.pi := by linarith
    have hd : (175205057/1000000000:ℝ) ≤ |(204927895/9244998:ℝ) - (7:ℝ)*Real.pi| ∧
        |(204927895/9244998:ℝ) - (7:ℝ)*Real.pi| ≤ (87602529/500000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (204927895/9244998:ℝ) (175205057/1000000000:ℝ) (87602529/500000000:ℝ) (40077483/250000000:ℝ)
      7 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((87602529/500000000:ℝ) - (175205057/1000000000:ℝ)^3/6 + (87602529/500000000:ℝ)^5/100)^2 + (40077483/250000000:ℝ) ≤ (1907/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
