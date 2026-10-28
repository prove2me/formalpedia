-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_group_00
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:47:39.822989+00:00
-- url     : https://prove2.me/submissions/13db20b6-e8e9-4155-88d5-616eeb4ffad6

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+0))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+0)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+0):ℝ)/10000 := by
  fin_cases i
  ·
    have hx : |x - (20162485/1320714:ℝ)| ≤ (157100629/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (20162485/1320714:ℝ) - (5:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (55201391/125000000:ℝ) ≤ |(20162485/1320714:ℝ) - (5:ℝ)*Real.pi| ∧
        |(20162485/1320714:ℝ) - (5:ℝ)*Real.pi| ≤ (441611129/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (20162485/1320714:ℝ) (55201391/125000000:ℝ) (441611129/1000000000:ℝ) (157100629/1000000000:ℝ)
      5 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((441611129/1000000000:ℝ) - (55201391/125000000:ℝ)^3/6 + (441611129/1000000000:ℝ)^5/100)^2 + (157100629/1000000000:ℝ) ≤ (3398/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (143910895/9244998:ℝ)| ≤ (39310041/250000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (143910895/9244998:ℝ) - (5:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (141611063/1000000000:ℝ) ≤ |(143910895/9244998:ℝ) - (5:ℝ)*Real.pi| ∧
        |(143910895/9244998:ℝ) - (5:ℝ)*Real.pi| ≤ (17701383/125000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (143910895/9244998:ℝ) (141611063/1000000000:ℝ) (17701383/125000000:ℝ) (39310041/250000000:ℝ)
      5 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((17701383/125000000:ℝ) - (141611063/1000000000:ℝ)^3/6 + (17701383/125000000:ℝ)^5/100)^2 + (39310041/250000000:ℝ) ≤ (1772/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (146684395/9244998:ℝ)| ≤ (157379699/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (146684395/9244998:ℝ) - (5:ℝ)*Real.pi := by linarith
    have hd : (158389001/1000000000:ℝ) ≤ |(146684395/9244998:ℝ) - (5:ℝ)*Real.pi| ∧
        |(146684395/9244998:ℝ) - (5:ℝ)*Real.pi| ≤ (79194501/500000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (146684395/9244998:ℝ) (158389001/1000000000:ℝ) (79194501/500000000:ℝ) (157379699/1000000000:ℝ)
      5 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((79194501/500000000:ℝ) - (158389001/1000000000:ℝ)^3/6 + (79194501/500000000:ℝ)^5/100)^2 + (157379699/1000000000:ℝ) ≤ (1823/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (149457895/9244998:ℝ)| ≤ (78759617/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (149457895/9244998:ℝ) - (5:ℝ)*Real.pi := by linarith
    have hd : (229194533/500000000:ℝ) ≤ |(149457895/9244998:ℝ) - (5:ℝ)*Real.pi| ∧
        |(149457895/9244998:ℝ) - (5:ℝ)*Real.pi| ≤ (458389067/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (149457895/9244998:ℝ) (229194533/500000000:ℝ) (458389067/1000000000:ℝ) (78759617/500000000:ℝ)
      5 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((458389067/1000000000:ℝ) - (229194533/500000000:ℝ)^3/6 + (458389067/1000000000:ℝ)^5/100)^2 + (78759617/500000000:ℝ) ≤ (3534/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (152231395/9244998:ℝ)| ≤ (157658769/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (152231395/9244998:ℝ) - (5:ℝ)*Real.pi := by linarith
    have hd : (758389131/1000000000:ℝ) ≤ |(152231395/9244998:ℝ) - (5:ℝ)*Real.pi| ∧
        |(152231395/9244998:ℝ) - (5:ℝ)*Real.pi| ≤ (189597283/250000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (152231395/9244998:ℝ) (758389131/1000000000:ℝ) (189597283/250000000:ℝ) (157658769/1000000000:ℝ)
      5 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((189597283/250000000:ℝ) - (758389131/1000000000:ℝ)^3/6 + (189597283/250000000:ℝ)^5/100)^2 + (157658769/1000000000:ℝ) ≤ (6313/10000:ℝ) := by norm_num
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
    have hx : |x - (166098895/9244998:ℝ)| ≤ (39589111/250000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (166098895/9244998:ℝ) - (6:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (883203197/1000000000:ℝ) ≤ |(166098895/9244998:ℝ) - (6:ℝ)*Real.pi| ∧
        |(166098895/9244998:ℝ) - (6:ℝ)*Real.pi| ≤ (441601599/500000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (166098895/9244998:ℝ) (883203197/1000000000:ℝ) (441601599/500000000:ℝ) (39589111/250000000:ℝ)
      6 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((441601599/500000000:ℝ) - (883203197/1000000000:ℝ)^3/6 + (441601599/500000000:ℝ)^5/100)^2 + (39589111/250000000:ℝ) ≤ (7571/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (168872395/9244998:ℝ)| ≤ (158495979/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (168872395/9244998:ℝ) - (6:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (145800783/250000000:ℝ) ≤ |(168872395/9244998:ℝ) - (6:ℝ)*Real.pi| ∧
        |(168872395/9244998:ℝ) - (6:ℝ)*Real.pi| ≤ (583203133/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (168872395/9244998:ℝ) (145800783/250000000:ℝ) (583203133/1000000000:ℝ) (158495979/1000000000:ℝ)
      6 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((583203133/1000000000:ℝ) - (145800783/250000000:ℝ)^3/6 + (583203133/1000000000:ℝ)^5/100)^2 + (158495979/1000000000:ℝ) ≤ (4619/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (171645895/9244998:ℝ)| ≤ (158635513/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (171645895/9244998:ℝ) - (6:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (283203067/1000000000:ℝ) ≤ |(171645895/9244998:ℝ) - (6:ℝ)*Real.pi| ∧
        |(171645895/9244998:ℝ) - (6:ℝ)*Real.pi| ≤ (70800767/250000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (171645895/9244998:ℝ) (283203067/1000000000:ℝ) (70800767/250000000:ℝ) (158635513/1000000000:ℝ)
      6 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((70800767/250000000:ℝ) - (283203067/1000000000:ℝ)^3/6 + (70800767/250000000:ℝ)^5/100)^2 + (158635513/1000000000:ℝ) ≤ (2368/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
