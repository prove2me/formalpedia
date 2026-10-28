-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_group_04
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:50:01.411766+00:00
-- url     : https://prove2.me/submissions/67c7fb40-76eb-4b68-b580-679acd6613ff

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+48))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+48)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+48):ℝ)/10000 := by
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
    have hx : |x - (282585895/9244998:ℝ)| ≤ (16421691/100000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (282585895/9244998:ℝ) - (10:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (424785543/500000000:ℝ) ≤ |(282585895/9244998:ℝ) - (10:ℝ)*Real.pi| ∧
        |(282585895/9244998:ℝ) - (10:ℝ)*Real.pi| ≤ (849571087/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (282585895/9244998:ℝ) (424785543/500000000:ℝ) (849571087/1000000000:ℝ) (16421691/100000000:ℝ)
      10 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((849571087/1000000000:ℝ) - (424785543/500000000:ℝ)^3/6 + (849571087/1000000000:ℝ)^5/100)^2 + (16421691/100000000:ℝ) ≤ (7295/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (285359395/9244998:ℝ)| ≤ (32871289/200000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (285359395/9244998:ℝ) - (10:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (549571021/1000000000:ℝ) ≤ |(285359395/9244998:ℝ) - (10:ℝ)*Real.pi| ∧
        |(285359395/9244998:ℝ) - (10:ℝ)*Real.pi| ≤ (274785511/500000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (285359395/9244998:ℝ) (549571021/1000000000:ℝ) (274785511/500000000:ℝ) (32871289/200000000:ℝ)
      10 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((274785511/500000000:ℝ) - (549571021/1000000000:ℝ)^3/6 + (274785511/500000000:ℝ)^5/100)^2 + (32871289/200000000:ℝ) ≤ (4373/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (288132895/9244998:ℝ)| ≤ (8224799/50000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (288132895/9244998:ℝ) - (10:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (62392739/250000000:ℝ) ≤ |(288132895/9244998:ℝ) - (10:ℝ)*Real.pi| ∧
        |(288132895/9244998:ℝ) - (10:ℝ)*Real.pi| ≤ (249570957/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (288132895/9244998:ℝ) (62392739/250000000:ℝ) (249570957/1000000000:ℝ) (8224799/50000000:ℝ)
      10 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((249570957/1000000000:ℝ) - (62392739/250000000:ℝ)^3/6 + (249570957/1000000000:ℝ)^5/100)^2 + (8224799/50000000:ℝ) ≤ (2255/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (290906395/9244998:ℝ)| ≤ (32927103/200000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (290906395/9244998:ℝ) - (10:ℝ)*Real.pi := by linarith
    have hd : (12607277/250000000:ℝ) ≤ |(290906395/9244998:ℝ) - (10:ℝ)*Real.pi| ∧
        |(290906395/9244998:ℝ) - (10:ℝ)*Real.pi| ≤ (50429109/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (290906395/9244998:ℝ) (12607277/250000000:ℝ) (50429109/1000000000:ℝ) (32927103/200000000:ℝ)
      10 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((50429109/1000000000:ℝ) - (12607277/250000000:ℝ)^3/6 + (50429109/1000000000:ℝ)^5/100)^2 + (32927103/200000000:ℝ) ≤ (1672/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (293679895/9244998:ℝ)| ≤ (3295501/20000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (293679895/9244998:ℝ) - (10:ℝ)*Real.pi := by linarith
    have hd : (350429173/1000000000:ℝ) ≤ |(293679895/9244998:ℝ) - (10:ℝ)*Real.pi| ∧
        |(293679895/9244998:ℝ) - (10:ℝ)*Real.pi| ≤ (175214587/500000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (293679895/9244998:ℝ) (350429173/1000000000:ℝ) (175214587/500000000:ℝ) (3295501/20000000:ℝ)
      10 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((175214587/500000000:ℝ) - (350429173/1000000000:ℝ)^3/6 + (175214587/500000000:ℝ)^5/100)^2 + (3295501/20000000:ℝ) ≤ (2827/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (42350485/1320714:ℝ)| ≤ (32982917/200000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (42350485/1320714:ℝ) - (10:ℝ)*Real.pi := by linarith
    have hd : (325214619/500000000:ℝ) ≤ |(42350485/1320714:ℝ) - (10:ℝ)*Real.pi| ∧
        |(42350485/1320714:ℝ) - (10:ℝ)*Real.pi| ≤ (650429239/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (42350485/1320714:ℝ) (325214619/500000000:ℝ) (650429239/1000000000:ℝ) (32982917/200000000:ℝ)
      10 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((650429239/1000000000:ℝ) - (325214619/500000000:ℝ)^3/6 + (650429239/1000000000:ℝ)^5/100)^2 + (32982917/200000000:ℝ) ≤ (5319/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (299226895/9244998:ℝ)| ≤ (165054119/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (299226895/9244998:ℝ) - (10:ℝ)*Real.pi := by linarith
    have hd : (950429303/1000000000:ℝ) ≤ |(299226895/9244998:ℝ) - (10:ℝ)*Real.pi| ∧
        |(299226895/9244998:ℝ) - (10:ℝ)*Real.pi| ≤ (118803663/125000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (299226895/9244998:ℝ) (950429303/1000000000:ℝ) (118803663/125000000:ℝ) (165054119/1000000000:ℝ)
      10 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((118803663/125000000:ℝ) - (950429303/1000000000:ℝ)^3/6 + (118803663/125000000:ℝ)^5/100)^2 + (165054119/1000000000:ℝ) ≤ (8295/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have h := Real.sin_sq_le_one x
    simpa [TaoFivePrimes.sineBinNumerator65k] using h
  ·
    have h := Real.sin_sq_le_one x
    simpa [TaoFivePrimes.sineBinNumerator65k] using h
