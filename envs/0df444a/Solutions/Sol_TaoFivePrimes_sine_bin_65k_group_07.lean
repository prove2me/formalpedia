-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_group_07
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:50:28.471325+00:00
-- url     : https://prove2.me/submissions/44a632ef-1bd8-4ff4-b242-72f0a7a9357f

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+84))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+84)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+84):ℝ)/10000 := by
  fin_cases i
  ·
    have hx : |x - (53444485/1320714:ℝ)| ≤ (84410781/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (53444485/1320714:ℝ) - (13:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (74869381/200000000:ℝ) ≤ |(53444485/1320714:ℝ) - (13:ℝ)*Real.pi| ∧
        |(53444485/1320714:ℝ) - (13:ℝ)*Real.pi| ≤ (187173453/500000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (53444485/1320714:ℝ) (74869381/200000000:ℝ) (187173453/500000000:ℝ) (84410781/500000000:ℝ)
      13 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((187173453/500000000:ℝ) - (74869381/200000000:ℝ)^3/6 + (187173453/500000000:ℝ)^5/100)^2 + (84410781/500000000:ℝ) ≤ (3026/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (376884895/9244998:ℝ)| ≤ (168961097/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (376884895/9244998:ℝ) - (13:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (1858671/25000000:ℝ) ≤ |(376884895/9244998:ℝ) - (13:ℝ)*Real.pi| ∧
        |(376884895/9244998:ℝ) - (13:ℝ)*Real.pi| ≤ (74346841/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (376884895/9244998:ℝ) (1858671/25000000:ℝ) (74346841/1000000000:ℝ) (168961097/1000000000:ℝ)
      13 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((74346841/1000000000:ℝ) - (1858671/25000000:ℝ)^3/6 + (74346841/1000000000:ℝ)^5/100)^2 + (168961097/1000000000:ℝ) ≤ (1745/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (379658395/9244998:ℝ)| ≤ (21137579/125000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (379658395/9244998:ℝ) - (13:ℝ)*Real.pi := by linarith
    have hd : (28206653/125000000:ℝ) ≤ |(379658395/9244998:ℝ) - (13:ℝ)*Real.pi| ∧
        |(379658395/9244998:ℝ) - (13:ℝ)*Real.pi| ≤ (9026129/40000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (379658395/9244998:ℝ) (28206653/125000000:ℝ) (9026129/40000000:ℝ) (21137579/125000000:ℝ)
      13 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((9026129/40000000:ℝ) - (28206653/125000000:ℝ)^3/6 + (9026129/40000000:ℝ)^5/100)^2 + (21137579/125000000:ℝ) ≤ (2192/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (382431895/9244998:ℝ)| ≤ (169240167/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (382431895/9244998:ℝ) - (13:ℝ)*Real.pi := by linarith
    have hd : (525653289/1000000000:ℝ) ≤ |(382431895/9244998:ℝ) - (13:ℝ)*Real.pi| ∧
        |(382431895/9244998:ℝ) - (13:ℝ)*Real.pi| ≤ (52565329/100000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (382431895/9244998:ℝ) (525653289/1000000000:ℝ) (52565329/100000000:ℝ) (169240167/1000000000:ℝ)
      13 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((52565329/100000000:ℝ) - (525653289/1000000000:ℝ)^3/6 + (52565329/100000000:ℝ)^5/100)^2 + (169240167/1000000000:ℝ) ≤ (4211/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (385205395/9244998:ℝ)| ≤ (84689851/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (385205395/9244998:ℝ) - (13:ℝ)*Real.pi := by linarith
    have hd : (412826677/500000000:ℝ) ≤ |(385205395/9244998:ℝ) - (13:ℝ)*Real.pi| ∧
        |(385205395/9244998:ℝ) - (13:ℝ)*Real.pi| ≤ (165130671/200000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (385205395/9244998:ℝ) (412826677/500000000:ℝ) (165130671/200000000:ℝ) (84689851/500000000:ℝ)
      13 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((165130671/200000000:ℝ) - (412826677/500000000:ℝ)^3/6 + (165130671/200000000:ℝ)^5/100)^2 + (84689851/500000000:ℝ) ≤ (7107/10000:ℝ) := by norm_num
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
    have hx : |x - (399072895/9244998:ℝ)| ≤ (2657459/15625000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (399072895/9244998:ℝ) - (14:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (407969487/500000000:ℝ) ≤ |(399072895/9244998:ℝ) - (14:ℝ)*Real.pi| ∧
        |(399072895/9244998:ℝ) - (14:ℝ)*Real.pi| ≤ (32637559/40000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (399072895/9244998:ℝ) (407969487/500000000:ℝ) (32637559/40000000:ℝ) (2657459/15625000:ℝ)
      14 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((32637559/40000000:ℝ) - (407969487/500000000:ℝ)^3/6 + (32637559/40000000:ℝ)^5/100)^2 + (2657459/15625000:ℝ) ≤ (7016/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (401846395/9244998:ℝ)| ≤ (170216911/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (401846395/9244998:ℝ) - (14:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (515938909/1000000000:ℝ) ≤ |(401846395/9244998:ℝ) - (14:ℝ)*Real.pi| ∧
        |(401846395/9244998:ℝ) - (14:ℝ)*Real.pi| ≤ (51593891/100000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (401846395/9244998:ℝ) (515938909/1000000000:ℝ) (51593891/100000000:ℝ) (170216911/1000000000:ℝ)
      14 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((51593891/100000000:ℝ) - (515938909/1000000000:ℝ)^3/6 + (51593891/100000000:ℝ)^5/100)^2 + (170216911/1000000000:ℝ) ≤ (4137/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (404619895/9244998:ℝ)| ≤ (85178223/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (404619895/9244998:ℝ) - (14:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (53984711/250000000:ℝ) ≤ |(404619895/9244998:ℝ) - (14:ℝ)*Real.pi| ∧
        |(404619895/9244998:ℝ) - (14:ℝ)*Real.pi| ≤ (43187769/200000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (404619895/9244998:ℝ) (53984711/250000000:ℝ) (43187769/200000000:ℝ) (85178223/500000000:ℝ)
      14 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((43187769/200000000:ℝ) - (53984711/250000000:ℝ)^3/6 + (43187769/200000000:ℝ)^5/100)^2 + (85178223/500000000:ℝ) ≤ (2163/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
