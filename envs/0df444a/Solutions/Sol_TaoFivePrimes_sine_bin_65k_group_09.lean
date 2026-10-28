-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_group_09
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:50:42.641229+00:00
-- url     : https://prove2.me/submissions/ab7e8627-68f0-49df-8c32-749006598cb7

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+108))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+108)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+108):ℝ)/10000 := by
  fin_cases i
  ·
    have hx : |x - (440675395/9244998:ℝ)| ≤ (215213/1250000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (440675395/9244998:ℝ) - (15:ℝ)*Real.pi := by linarith
    have hd : (108493869/200000000:ℝ) ≤ |(440675395/9244998:ℝ) - (15:ℝ)*Real.pi| ∧
        |(440675395/9244998:ℝ) - (15:ℝ)*Real.pi| ≤ (271234673/500000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (440675395/9244998:ℝ) (108493869/200000000:ℝ) (271234673/500000000:ℝ) (215213/1250000:ℝ)
      15 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((271234673/500000000:ℝ) - (108493869/200000000:ℝ)^3/6 + (271234673/500000000:ℝ)^5/100)^2 + (215213/1250000:ℝ) ≤ (4388/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (443448895/9244998:ℝ)| ≤ (34461987/200000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (443448895/9244998:ℝ) - (15:ℝ)*Real.pi := by linarith
    have hd : (84246941/100000000:ℝ) ≤ |(443448895/9244998:ℝ) - (15:ℝ)*Real.pi| ∧
        |(443448895/9244998:ℝ) - (15:ℝ)*Real.pi| ≤ (842469411/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (443448895/9244998:ℝ) (84246941/100000000:ℝ) (842469411/1000000000:ℝ) (34461987/200000000:ℝ)
      15 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((842469411/1000000000:ℝ) - (84246941/100000000:ℝ)^3/6 + (842469411/1000000000:ℝ)^5/100)^2 + (34461987/200000000:ℝ) ≤ (7305/10000:ℝ) := by norm_num
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
    have hx : |x - (457316395/9244998:ℝ)| ≤ (17300761/100000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (457316395/9244998:ℝ) - (16:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (799122919/1000000000:ℝ) ≤ |(457316395/9244998:ℝ) - (16:ℝ)*Real.pi| ∧
        |(457316395/9244998:ℝ) - (16:ℝ)*Real.pi| ≤ (19978073/25000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (457316395/9244998:ℝ) (799122919/1000000000:ℝ) (19978073/25000000:ℝ) (17300761/100000000:ℝ)
      16 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((19978073/25000000:ℝ) - (799122919/1000000000:ℝ)^3/6 + (19978073/25000000:ℝ)^5/100)^2 + (17300761/100000000:ℝ) ≤ (6876/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (460089895/9244998:ℝ)| ≤ (34629429/200000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (460089895/9244998:ℝ) - (16:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (249561427/500000000:ℝ) ≤ |(460089895/9244998:ℝ) - (16:ℝ)*Real.pi| ∧
        |(460089895/9244998:ℝ) - (16:ℝ)*Real.pi| ≤ (99824571/200000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (460089895/9244998:ℝ) (249561427/500000000:ℝ) (99824571/200000000:ℝ) (34629429/200000000:ℝ)
      16 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((99824571/200000000:ℝ) - (249561427/500000000:ℝ)^3/6 + (99824571/200000000:ℝ)^5/100)^2 + (34629429/200000000:ℝ) ≤ (4024/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (462863395/9244998:ℝ)| ≤ (173286679/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (462863395/9244998:ℝ) - (16:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (199122789/1000000000:ℝ) ≤ |(462863395/9244998:ℝ) - (16:ℝ)*Real.pi| ∧
        |(462863395/9244998:ℝ) - (16:ℝ)*Real.pi| ≤ (19912279/100000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (462863395/9244998:ℝ) (199122789/1000000000:ℝ) (19912279/100000000:ℝ) (173286679/1000000000:ℝ)
      16 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((19912279/100000000:ℝ) - (199122789/1000000000:ℝ)^3/6 + (19912279/100000000:ℝ)^5/100)^2 + (173286679/1000000000:ℝ) ≤ (2125/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (465636895/9244998:ℝ)| ≤ (86713107/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (465636895/9244998:ℝ) - (16:ℝ)*Real.pi := by linarith
    have hd : (4035091/40000000:ℝ) ≤ |(465636895/9244998:ℝ) - (16:ℝ)*Real.pi| ∧
        |(465636895/9244998:ℝ) - (16:ℝ)*Real.pi| ≤ (25219319/250000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (465636895/9244998:ℝ) (4035091/40000000:ℝ) (25219319/250000000:ℝ) (86713107/500000000:ℝ)
      16 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((25219319/250000000:ℝ) - (4035091/40000000:ℝ)^3/6 + (25219319/250000000:ℝ)^5/100)^2 + (86713107/500000000:ℝ) ≤ (1836/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (468410395/9244998:ℝ)| ≤ (173565749/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (468410395/9244998:ℝ) - (16:ℝ)*Real.pi := by linarith
    have hd : (20043867/50000000:ℝ) ≤ |(468410395/9244998:ℝ) - (16:ℝ)*Real.pi| ∧
        |(468410395/9244998:ℝ) - (16:ℝ)*Real.pi| ≤ (400877341/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (468410395/9244998:ℝ) (20043867/50000000:ℝ) (400877341/1000000000:ℝ) (173565749/1000000000:ℝ)
      16 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((400877341/1000000000:ℝ) - (20043867/50000000:ℝ)^3/6 + (400877341/1000000000:ℝ)^5/100)^2 + (173565749/1000000000:ℝ) ≤ (3259/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (67311985/1320714:ℝ)| ≤ (43426321/250000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (67311985/1320714:ℝ) - (16:ℝ)*Real.pi := by linarith
    have hd : (140175481/200000000:ℝ) ≤ |(67311985/1320714:ℝ) - (16:ℝ)*Real.pi| ∧
        |(67311985/1320714:ℝ) - (16:ℝ)*Real.pi| ≤ (350438703/500000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (67311985/1320714:ℝ) (140175481/200000000:ℝ) (350438703/500000000:ℝ) (43426321/250000000:ℝ)
      16 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((350438703/500000000:ℝ) - (140175481/200000000:ℝ)^3/6 + (350438703/500000000:ℝ)^5/100)^2 + (43426321/250000000:ℝ) ≤ (5900/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
