-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_group_11
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:51:08.011331+00:00
-- url     : https://prove2.me/submissions/ae6696ff-c53a-4763-a339-6cc8c1e25470

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+132))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+132)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+132):ℝ)/10000 := by
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
    have hx : |x - (515559895/9244998:ℝ)| ≤ (175937843/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (515559895/9244998:ℝ) - (18:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (782306863/1000000000:ℝ) ≤ |(515559895/9244998:ℝ) - (18:ℝ)*Real.pi| ∧
        |(515559895/9244998:ℝ) - (18:ℝ)*Real.pi| ≤ (48894179/62500000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (515559895/9244998:ℝ) (782306863/1000000000:ℝ) (48894179/62500000:ℝ) (175937843/1000000000:ℝ)
      18 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((48894179/62500000:ℝ) - (782306863/1000000000:ℝ)^3/6 + (48894179/62500000:ℝ)^5/100)^2 + (175937843/1000000000:ℝ) ≤ (6736/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (518333395/9244998:ℝ)| ≤ (88038689/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (518333395/9244998:ℝ) - (18:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (241153399/500000000:ℝ) ≤ |(518333395/9244998:ℝ) - (18:ℝ)*Real.pi| ∧
        |(518333395/9244998:ℝ) - (18:ℝ)*Real.pi| ≤ (482306799/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (518333395/9244998:ℝ) (241153399/500000000:ℝ) (482306799/1000000000:ℝ) (88038689/500000000:ℝ)
      18 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((482306799/1000000000:ℝ) - (241153399/500000000:ℝ)^3/6 + (482306799/1000000000:ℝ)^5/100)^2 + (88038689/500000000:ℝ) ≤ (3913/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (521106895/9244998:ℝ)| ≤ (176216913/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (521106895/9244998:ℝ) - (18:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (182306733/1000000000:ℝ) ≤ |(521106895/9244998:ℝ) - (18:ℝ)*Real.pi| ∧
        |(521106895/9244998:ℝ) - (18:ℝ)*Real.pi| ≤ (91153367/500000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (521106895/9244998:ℝ) (182306733/1000000000:ℝ) (91153367/500000000:ℝ) (176216913/1000000000:ℝ)
      18 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((91153367/500000000:ℝ) - (182306733/1000000000:ℝ)^3/6 + (91153367/500000000:ℝ)^5/100)^2 + (176216913/1000000000:ℝ) ≤ (2091/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (523880395/9244998:ℝ)| ≤ (5511139/31250000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (523880395/9244998:ℝ) - (18:ℝ)*Real.pi := by linarith
    have hd : (117693331/1000000000:ℝ) ≤ |(523880395/9244998:ℝ) - (18:ℝ)*Real.pi| ∧
        |(523880395/9244998:ℝ) - (18:ℝ)*Real.pi| ≤ (29423333/250000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (523880395/9244998:ℝ) (117693331/1000000000:ℝ) (29423333/250000000:ℝ) (5511139/31250000:ℝ)
      18 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((29423333/250000000:ℝ) - (117693331/1000000000:ℝ)^3/6 + (29423333/250000000:ℝ)^5/100)^2 + (5511139/31250000:ℝ) ≤ (1902/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (1715485/30114:ℝ)| ≤ (88247991/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (1715485/30114:ℝ) - (18:ℝ)*Real.pi := by linarith
    have hd : (104423349/250000000:ℝ) ≤ |(1715485/30114:ℝ) - (18:ℝ)*Real.pi| ∧
        |(1715485/30114:ℝ) - (18:ℝ)*Real.pi| ≤ (417693397/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (1715485/30114:ℝ) (104423349/250000000:ℝ) (417693397/1000000000:ℝ) (88247991/500000000:ℝ)
      18 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((417693397/1000000000:ℝ) - (104423349/250000000:ℝ)^3/6 + (417693397/1000000000:ℝ)^5/100)^2 + (88247991/500000000:ℝ) ≤ (3411/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (75632485/1320714:ℝ)| ≤ (176635517/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (75632485/1320714:ℝ) - (18:ℝ)*Real.pi := by linarith
    have hd : (717693461/1000000000:ℝ) ≤ |(75632485/1320714:ℝ) - (18:ℝ)*Real.pi| ∧
        |(75632485/1320714:ℝ) - (18:ℝ)*Real.pi| ≤ (358846731/500000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (75632485/1320714:ℝ) (717693461/1000000000:ℝ) (358846731/500000000:ℝ) (176635517/1000000000:ℝ)
      18 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((358846731/500000000:ℝ) - (717693461/1000000000:ℝ)^3/6 + (358846731/500000000:ℝ)^5/100)^2 + (176635517/1000000000:ℝ) ≤ (6096/10000:ℝ) := by norm_num
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
