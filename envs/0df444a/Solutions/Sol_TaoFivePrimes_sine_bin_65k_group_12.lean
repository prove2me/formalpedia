-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_group_12
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:51:22.319545+00:00
-- url     : https://prove2.me/submissions/c5456123-e4d1-4ed6-97f0-8006df950708

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem solution (i : Fin 12) (x : ℝ)
    (hx0 : (65000+1290*((i.val:ℝ)+144))/(2*2151) ≤ x)
    (hx1 : x ≤ (65000+1290*((i.val:ℝ)+144)+1290)/(2*2149)) :
    (Real.sin x)^2 ≤ (TaoFivePrimes.sineBinNumerator65k (i.val+144):ℝ)/10000 := by
  fin_cases i
  ·
    have h := Real.sin_sq_le_one x
    simpa [TaoFivePrimes.sineBinNumerator65k] using h
  ·
    have hx : |x - (543294895/9244998:ℝ)| ≤ (22166649/125000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (543294895/9244998:ℝ) - (19:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (923898867/1000000000:ℝ) ≤ |(543294895/9244998:ℝ) - (19:ℝ)*Real.pi| ∧
        |(543294895/9244998:ℝ) - (19:ℝ)*Real.pi| ≤ (230974717/250000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (543294895/9244998:ℝ) (923898867/1000000000:ℝ) (230974717/250000000:ℝ) (22166649/125000000:ℝ)
      19 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((230974717/250000000:ℝ) - (923898867/1000000000:ℝ)^3/6 + (230974717/250000000:ℝ)^5/100)^2 + (22166649/125000000:ℝ) ≤ (8161/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (2284805/38682:ℝ)| ≤ (177472727/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (2284805/38682:ℝ) - (19:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (311949401/500000000:ℝ) ≤ |(2284805/38682:ℝ) - (19:ℝ)*Real.pi| ∧
        |(2284805/38682:ℝ) - (19:ℝ)*Real.pi| ≤ (623898803/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (2284805/38682:ℝ) (311949401/500000000:ℝ) (623898803/1000000000:ℝ) (177472727/1000000000:ℝ)
      19 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((623898803/1000000000:ℝ) - (311949401/500000000:ℝ)^3/6 + (623898803/1000000000:ℝ)^5/100)^2 + (177472727/1000000000:ℝ) ≤ (5190/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (78405985/1320714:ℝ)| ≤ (88806131/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (78405985/1320714:ℝ) - (19:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (161949369/500000000:ℝ) ≤ |(78405985/1320714:ℝ) - (19:ℝ)*Real.pi| ∧
        |(78405985/1320714:ℝ) - (19:ℝ)*Real.pi| ≤ (323898739/1000000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (78405985/1320714:ℝ) (161949369/500000000:ℝ) (323898739/1000000000:ℝ) (88806131/500000000:ℝ)
      19 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((323898739/1000000000:ℝ) - (161949369/500000000:ℝ)^3/6 + (323898739/1000000000:ℝ)^5/100)^2 + (88806131/500000000:ℝ) ≤ (2790/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (551615395/9244998:ℝ)| ≤ (177751797/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : (551615395/9244998:ℝ) - (19:ℝ)*Real.pi ≤ 0 := by linarith
    have hd : (23898673/1000000000:ℝ) ≤ |(551615395/9244998:ℝ) - (19:ℝ)*Real.pi| ∧
        |(551615395/9244998:ℝ) - (19:ℝ)*Real.pi| ≤ (11949337/500000000:ℝ) := by
      rw [abs_of_nonpos hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (551615395/9244998:ℝ) (23898673/1000000000:ℝ) (11949337/500000000:ℝ) (177751797/1000000000:ℝ)
      19 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((11949337/500000000:ℝ) - (23898673/1000000000:ℝ)^3/6 + (11949337/500000000:ℝ)^5/100)^2 + (177751797/1000000000:ℝ) ≤ (1784/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (554388895/9244998:ℝ)| ≤ (44472833/250000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (554388895/9244998:ℝ) - (19:ℝ)*Real.pi := by linarith
    have hd : (276101391/1000000000:ℝ) ≤ |(554388895/9244998:ℝ) - (19:ℝ)*Real.pi| ∧
        |(554388895/9244998:ℝ) - (19:ℝ)*Real.pi| ≤ (17256337/62500000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (554388895/9244998:ℝ) (276101391/1000000000:ℝ) (17256337/62500000:ℝ) (44472833/250000000:ℝ)
      19 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((17256337/62500000:ℝ) - (276101391/1000000000:ℝ)^3/6 + (17256337/62500000:ℝ)^5/100)^2 + (44472833/250000000:ℝ) ≤ (2523/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (557162395/9244998:ℝ)| ≤ (89015433/500000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (557162395/9244998:ℝ) - (19:ℝ)*Real.pi := by linarith
    have hd : (36006341/62500000:ℝ) ≤ |(557162395/9244998:ℝ) - (19:ℝ)*Real.pi| ∧
        |(557162395/9244998:ℝ) - (19:ℝ)*Real.pi| ≤ (576101457/1000000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (557162395/9244998:ℝ) (36006341/62500000:ℝ) (576101457/1000000000:ℝ) (89015433/500000000:ℝ)
      19 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((576101457/1000000000:ℝ) - (36006341/62500000:ℝ)^3/6 + (576101457/1000000000:ℝ)^5/100)^2 + (89015433/500000000:ℝ) ≤ (4750/10000:ℝ) := by norm_num
    have hh := h.trans hn
    simpa [TaoFivePrimes.sineBinNumerator65k] using hh
  ·
    have hx : |x - (559935895/9244998:ℝ)| ≤ (178170401/1000000000:ℝ) := by
      rw [abs_le]
      constructor <;> norm_num at hx0 hx1 ⊢ <;> linarith
    have hpl : (3141592653589783/10^15:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
    have hpu : Real.pi ≤ (3141592653589803/10^15:ℝ) := by linarith [Real.pi_lt_d20]
    have hs : 0 ≤ (559935895/9244998:ℝ) - (19:ℝ)*Real.pi := by linarith
    have hd : (876101521/1000000000:ℝ) ≤ |(559935895/9244998:ℝ) - (19:ℝ)*Real.pi| ∧
        |(559935895/9244998:ℝ) - (19:ℝ)*Real.pi| ≤ (438050761/500000000:ℝ) := by
      rw [abs_of_nonneg hs]
      constructor <;> linarith
    have h := TaoFivePrimes.sine_squared_interval_enclosure x (559935895/9244998:ℝ) (876101521/1000000000:ℝ) (438050761/500000000:ℝ) (178170401/1000000000:ℝ)
      19 hx (by norm_num) hd.1 hd.2 (by norm_num)
    have hn : ((438050761/500000000:ℝ) - (876101521/1000000000:ℝ)^3/6 + (438050761/500000000:ℝ)^5/100)^2 + (178170401/1000000000:ℝ) ≤ (7699/10000:ℝ) := by norm_num
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
