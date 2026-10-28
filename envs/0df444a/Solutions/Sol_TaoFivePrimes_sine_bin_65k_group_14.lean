-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_group_14
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:49:01.053721+00:00
-- url     : https://prove2.me/submissions/f6fd14b6-3142-4283-b38b-e401ee0000de

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+168))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+168)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+168):ℝ)/10000 := by
  fin_cases i
  ·
    have hx : |x - (86726485/1320714:ℝ)| ≤ (36108499/200000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (86726485/1320714:ℝ) - (21:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (153541341/500000000:ℝ) ≤ |(86726485/1320714:ℝ) - (21:ℝ)*Real.pi| ∧
        |(86726485/1320714:ℝ) - (21:ℝ)*Real.pi| ≤ (307082683/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (86726485/1320714:ℝ) (153541341/500000000:ℝ) (307082683/1000000000:ℝ) (36108499/200000000:ℝ)
      21 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((307082683/1000000000:ℝ) - (153541341/500000000:ℝ)^3/6 + (307082683/1000000000:ℝ)^5/100)^2 + (36108499/200000000:ℝ) ≤ (2720/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (609858895/9244998:ℝ)| ≤ (18068203/100000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (609858895/9244998:ℝ) - (21:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (7082617/1000000000:ℝ) ≤ |(609858895/9244998:ℝ) - (21:ℝ)*Real.pi| ∧
        |(609858895/9244998:ℝ) - (21:ℝ)*Real.pi| ≤ (3541309/500000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (609858895/9244998:ℝ) (7082617/1000000000:ℝ) (3541309/500000000:ℝ) (18068203/100000000:ℝ)
      21 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((3541309/500000000:ℝ) - (7082617/1000000000:ℝ)^3/6 + (3541309/500000000:ℝ)^5/100)^2 + (18068203/100000000:ℝ) ≤ (1808/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (612632395/9244998:ℝ)| ≤ (36164313/200000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (612632395/9244998:ℝ) - (21:ℝ)*Real.pi := by linarith
    have hd : (292917447/1000000000:ℝ) ≤ |(612632395/9244998:ℝ) - (21:ℝ)*Real.pi| ∧
        |(612632395/9244998:ℝ) - (21:ℝ)*Real.pi| ≤ (36614681/125000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (612632395/9244998:ℝ) (292917447/1000000000:ℝ) (36614681/125000000:ℝ) (36164313/200000000:ℝ)
      21 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((36614681/125000000:ℝ) - (292917447/1000000000:ℝ)^3/6 + (36614681/125000000:ℝ)^5/100)^2 + (36164313/200000000:ℝ) ≤ (2642/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (615405895/9244998:ℝ)| ≤ (1809611/10000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (615405895/9244998:ℝ) - (21:ℝ)*Real.pi := by linarith
    have hd : (74114689/125000000:ℝ) ≤ |(615405895/9244998:ℝ) - (21:ℝ)*Real.pi| ∧
        |(615405895/9244998:ℝ) - (21:ℝ)*Real.pi| ≤ (592917513/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (615405895/9244998:ℝ) (74114689/125000000:ℝ) (592917513/1000000000:ℝ) (1809611/10000000:ℝ)
      21 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((592917513/1000000000:ℝ) - (74114689/125000000:ℝ)^3/6 + (592917513/1000000000:ℝ)^5/100)^2 + (1809611/10000000:ℝ) ≤ (4934/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (618179395/9244998:ℝ)| ≤ (36220127/200000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (618179395/9244998:ℝ) - (21:ℝ)*Real.pi := by linarith
    have hd : (892917577/1000000000:ℝ) ≤ |(618179395/9244998:ℝ) - (21:ℝ)*Real.pi| ∧
        |(618179395/9244998:ℝ) - (21:ℝ)*Real.pi| ≤ (446458789/500000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (618179395/9244998:ℝ) (892917577/1000000000:ℝ) (446458789/500000000:ℝ) (36220127/200000000:ℝ)
      21 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((446458789/500000000:ℝ) - (892917577/1000000000:ℝ)^3/6 + (446458789/500000000:ℝ)^5/100)^2 + (36220127/200000000:ℝ) ≤ (7895/10000:ℝ) := by norm_num
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
    have hx : |x - (632046895/9244998:ℝ)| ≤ (181798309/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (632046895/9244998:ℝ) - (22:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (748674751/1000000000:ℝ) ≤ |(632046895/9244998:ℝ) - (22:ℝ)*Real.pi| ∧
        |(632046895/9244998:ℝ) - (22:ℝ)*Real.pi| ≤ (11698043/15625000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (632046895/9244998:ℝ) (748674751/1000000000:ℝ) (11698043/15625000:ℝ) (181798309/1000000000:ℝ)
      22 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((11698043/15625000:ℝ) - (748674751/1000000000:ℝ)^3/6 + (11698043/15625000:ℝ)^5/100)^2 + (181798309/1000000000:ℝ) ≤ (6457/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (634820395/9244998:ℝ)| ≤ (45484461/250000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (634820395/9244998:ℝ) - (22:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (224337343/500000000:ℝ) ≤ |(634820395/9244998:ℝ) - (22:ℝ)*Real.pi| ∧
        |(634820395/9244998:ℝ) - (22:ℝ)*Real.pi| ≤ (448674687/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (634820395/9244998:ℝ) (224337343/500000000:ℝ) (448674687/1000000000:ℝ) (45484461/250000000:ℝ)
      22 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((448674687/1000000000:ℝ) - (224337343/500000000:ℝ)^3/6 + (448674687/1000000000:ℝ)^5/100)^2 + (45484461/250000000:ℝ) ≤ (3702/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (637593895/9244998:ℝ)| ≤ (182077379/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (637593895/9244998:ℝ) - (22:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (74337311/500000000:ℝ) ≤ |(637593895/9244998:ℝ) - (22:ℝ)*Real.pi| ∧
        |(637593895/9244998:ℝ) - (22:ℝ)*Real.pi| ≤ (148674623/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (637593895/9244998:ℝ) (74337311/500000000:ℝ) (148674623/1000000000:ℝ) (182077379/1000000000:ℝ)
      22 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((148674623/1000000000:ℝ) - (74337311/500000000:ℝ)^3/6 + (148674623/1000000000:ℝ)^5/100)^2 + (182077379/1000000000:ℝ) ≤ (2041/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
