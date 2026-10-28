-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_group_03
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:49:59.4595+00:00
-- url     : https://prove2.me/submissions/ec450f0c-6a2c-4165-b540-9bfd95bc7267

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+36))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+36)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+36):ℝ)/10000 := by
  fin_cases i
  ·
    have hx : |x - (240983395/9244998:ℝ)| ≤ (81061943/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (240983395/9244998:ℝ) - (8:ℝ)*Real.pi := by linarith
    have hd : (933613247/1000000000:ℝ) ≤ |(240983395/9244998:ℝ) - (8:ℝ)*Real.pi| ∧
        |(240983395/9244998:ℝ) - (8:ℝ)*Real.pi| ≤ (14587707/15625000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (240983395/9244998:ℝ) (933613247/1000000000:ℝ) (14587707/15625000:ℝ) (81061943/500000000:ℝ)
      8 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((14587707/15625000:ℝ) - (933613247/1000000000:ℝ)^3/6 + (14587707/15625000:ℝ)^5/100)^2 + (81061943/500000000:ℝ) ≤ (8103/10000:ℝ) := by norm_num
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
    have hx : |x - (254850895/9244998:ℝ)| ≤ (162821561/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (254850895/9244998:ℝ) - (9:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (707979081/1000000000:ℝ) ≤ |(254850895/9244998:ℝ) - (9:ℝ)*Real.pi| ∧
        |(254850895/9244998:ℝ) - (9:ℝ)*Real.pi| ≤ (353989541/500000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (254850895/9244998:ℝ) (707979081/1000000000:ℝ) (353989541/500000000:ℝ) (162821561/1000000000:ℝ)
      9 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((353989541/500000000:ℝ) - (707979081/1000000000:ℝ)^3/6 + (353989541/500000000:ℝ)^5/100)^2 + (162821561/1000000000:ℝ) ≤ (5862/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (36803485/1320714:ℝ)| ≤ (20370137/125000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (36803485/1320714:ℝ) - (9:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (50997377/125000000:ℝ) ≤ |(36803485/1320714:ℝ) - (9:ℝ)*Real.pi| ∧
        |(36803485/1320714:ℝ) - (9:ℝ)*Real.pi| ≤ (407979017/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (36803485/1320714:ℝ) (50997377/125000000:ℝ) (407979017/1000000000:ℝ) (20370137/125000000:ℝ)
      9 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((407979017/1000000000:ℝ) - (50997377/125000000:ℝ)^3/6 + (407979017/1000000000:ℝ)^5/100)^2 + (20370137/125000000:ℝ) ≤ (3204/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (260397895/9244998:ℝ)| ≤ (163100631/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (260397895/9244998:ℝ) - (9:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (107978951/1000000000:ℝ) ≤ |(260397895/9244998:ℝ) - (9:ℝ)*Real.pi| ∧
        |(260397895/9244998:ℝ) - (9:ℝ)*Real.pi| ≤ (13497369/125000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (260397895/9244998:ℝ) (107978951/1000000000:ℝ) (13497369/125000000:ℝ) (163100631/1000000000:ℝ)
      9 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((13497369/125000000:ℝ) - (107978951/1000000000:ℝ)^3/6 + (13497369/125000000:ℝ)^5/100)^2 + (163100631/1000000000:ℝ) ≤ (1748/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (263171395/9244998:ℝ)| ≤ (81620083/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (263171395/9244998:ℝ) - (9:ℝ)*Real.pi := by linarith
    have hd : (192021113/1000000000:ℝ) ≤ |(263171395/9244998:ℝ) - (9:ℝ)*Real.pi| ∧
        |(263171395/9244998:ℝ) - (9:ℝ)*Real.pi| ≤ (96010557/500000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (263171395/9244998:ℝ) (192021113/1000000000:ℝ) (96010557/500000000:ℝ) (81620083/500000000:ℝ)
      9 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((96010557/500000000:ℝ) - (192021113/1000000000:ℝ)^3/6 + (96010557/500000000:ℝ)^5/100)^2 + (81620083/500000000:ℝ) ≤ (1997/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (265944895/9244998:ℝ)| ≤ (163379701/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (265944895/9244998:ℝ) - (9:ℝ)*Real.pi := by linarith
    have hd : (246010589/500000000:ℝ) ≤ |(265944895/9244998:ℝ) - (9:ℝ)*Real.pi| ∧
        |(265944895/9244998:ℝ) - (9:ℝ)*Real.pi| ≤ (492021179/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (265944895/9244998:ℝ) (246010589/500000000:ℝ) (492021179/1000000000:ℝ) (163379701/1000000000:ℝ)
      9 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((492021179/1000000000:ℝ) - (246010589/500000000:ℝ)^3/6 + (492021179/1000000000:ℝ)^5/100)^2 + (163379701/1000000000:ℝ) ≤ (3866/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (268718395/9244998:ℝ)| ≤ (32703847/200000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (268718395/9244998:ℝ) - (9:ℝ)*Real.pi := by linarith
    have hd : (396010621/500000000:ℝ) ≤ |(268718395/9244998:ℝ) - (9:ℝ)*Real.pi| ∧
        |(268718395/9244998:ℝ) - (9:ℝ)*Real.pi| ≤ (792021243/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (268718395/9244998:ℝ) (396010621/500000000:ℝ) (792021243/1000000000:ℝ) (32703847/200000000:ℝ)
      9 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((792021243/1000000000:ℝ) - (396010621/500000000:ℝ)^3/6 + (792021243/1000000000:ℝ)^5/100)^2 + (32703847/200000000:ℝ) ≤ (6710/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have h := Real.sin_sq_le_one x
    simpa [TaoFivePrimes.sineBinNumerator65k] using h
