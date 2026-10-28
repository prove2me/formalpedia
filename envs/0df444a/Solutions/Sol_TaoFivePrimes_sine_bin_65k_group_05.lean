-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_group_05
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:50:03.639328+00:00
-- url     : https://prove2.me/submissions/0a687716-6357-430b-9139-0e2262bf8dcc

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+60))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+60)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+60):ℝ)/10000 := by
  fin_cases i
  ·
    have h := Real.sin_sq_le_one x
    simpa [TaoFivePrimes.sineBinNumerator65k] using h
  ·
    have hx : |x - (310320895/9244998:ℝ)| ≤ (165612259/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (310320895/9244998:ℝ) - (11:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (99116309/100000000:ℝ) ≤ |(310320895/9244998:ℝ) - (11:ℝ)*Real.pi| ∧
        |(310320895/9244998:ℝ) - (11:ℝ)*Real.pi| ≤ (991163091/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (310320895/9244998:ℝ) (99116309/100000000:ℝ) (991163091/1000000000:ℝ) (165612259/1000000000:ℝ)
      11 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((991163091/1000000000:ℝ) - (99116309/100000000:ℝ)^3/6 + (991163091/1000000000:ℝ)^5/100)^2 + (165612259/1000000000:ℝ) ≤ (8686/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (313094395/9244998:ℝ)| ≤ (82875897/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (313094395/9244998:ℝ) - (11:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (27646521/40000000:ℝ) ≤ |(313094395/9244998:ℝ) - (11:ℝ)*Real.pi| ∧
        |(313094395/9244998:ℝ) - (11:ℝ)*Real.pi| ≤ (345581513/500000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (313094395/9244998:ℝ) (27646521/40000000:ℝ) (345581513/500000000:ℝ) (82875897/500000000:ℝ)
      11 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((345581513/500000000:ℝ) - (27646521/40000000:ℝ)^3/6 + (345581513/500000000:ℝ)^5/100)^2 + (82875897/500000000:ℝ) ≤ (5725/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (45123985/1320714:ℝ)| ≤ (165891329/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (45123985/1320714:ℝ) - (11:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (4889537/12500000:ℝ) ≤ |(45123985/1320714:ℝ) - (11:ℝ)*Real.pi| ∧
        |(45123985/1320714:ℝ) - (11:ℝ)*Real.pi| ≤ (391162961/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (45123985/1320714:ℝ) (4889537/12500000:ℝ) (391162961/1000000000:ℝ) (165891329/1000000000:ℝ)
      11 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((391162961/1000000000:ℝ) - (4889537/12500000:ℝ)^3/6 + (391162961/1000000000:ℝ)^5/100)^2 + (165891329/1000000000:ℝ) ≤ (3113/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (318641395/9244998:ℝ)| ≤ (10376929/62500000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (318641395/9244998:ℝ) - (11:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (5697681/62500000:ℝ) ≤ |(318641395/9244998:ℝ) - (11:ℝ)*Real.pi| ∧
        |(318641395/9244998:ℝ) - (11:ℝ)*Real.pi| ≤ (91162897/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (318641395/9244998:ℝ) (5697681/62500000:ℝ) (91162897/1000000000:ℝ) (10376929/62500000:ℝ)
      11 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((91162897/1000000000:ℝ) - (5697681/62500000:ℝ)^3/6 + (91162897/1000000000:ℝ)^5/100)^2 + (10376929/62500000:ℝ) ≤ (1744/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (321414895/9244998:ℝ)| ≤ (166170399/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (321414895/9244998:ℝ) - (11:ℝ)*Real.pi := by linarith
    have hd : (13052323/62500000:ℝ) ≤ |(321414895/9244998:ℝ) - (11:ℝ)*Real.pi| ∧
        |(321414895/9244998:ℝ) - (11:ℝ)*Real.pi| ≤ (208837169/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (321414895/9244998:ℝ) (13052323/62500000:ℝ) (208837169/1000000000:ℝ) (166170399/1000000000:ℝ)
      11 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((208837169/1000000000:ℝ) - (13052323/62500000:ℝ)^3/6 + (208837169/1000000000:ℝ)^5/100)^2 + (166170399/1000000000:ℝ) ≤ (2092/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (324188395/9244998:ℝ)| ≤ (83154967/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (324188395/9244998:ℝ) - (11:ℝ)*Real.pi := by linarith
    have hd : (508837233/1000000000:ℝ) ≤ |(324188395/9244998:ℝ) - (11:ℝ)*Real.pi| ∧
        |(324188395/9244998:ℝ) - (11:ℝ)*Real.pi| ≤ (254418617/500000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (324188395/9244998:ℝ) (508837233/1000000000:ℝ) (254418617/500000000:ℝ) (83154967/500000000:ℝ)
      11 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((254418617/500000000:ℝ) - (508837233/1000000000:ℝ)^3/6 + (254418617/500000000:ℝ)^5/100)^2 + (83154967/500000000:ℝ) ≤ (4037/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (326961895/9244998:ℝ)| ≤ (166449469/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (326961895/9244998:ℝ) - (11:ℝ)*Real.pi := by linarith
    have hd : (404418649/500000000:ℝ) ≤ |(326961895/9244998:ℝ) - (11:ℝ)*Real.pi| ∧
        |(326961895/9244998:ℝ) - (11:ℝ)*Real.pi| ≤ (808837299/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (326961895/9244998:ℝ) (404418649/500000000:ℝ) (808837299/1000000000:ℝ) (166449469/1000000000:ℝ)
      11 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((808837299/1000000000:ℝ) - (404418649/500000000:ℝ)^3/6 + (808837299/1000000000:ℝ)^5/100)^2 + (166449469/1000000000:ℝ) ≤ (6908/10000:ℝ) := by norm_num
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
