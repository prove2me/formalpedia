-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.two_moment_continuous_optimum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:33:35.947728+00:00
-- url     : https://prove2.me/submissions/63a6ee91-edd8-442e-a770-b1862da5faee

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

open scoped BigOperators ENNReal
open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution (r1 r2 : ℝ) (h2 : 0<r2) (hle : r2≤r1) :
    alphaC ![r1,r2] = ENNReal.ofReal (r1*Real.sqrt r1/Real.sqrt r2) ∧
    continuousFeasible ![r1,r2]
      (ENNReal.ofReal (r1^2/r2) • Measure.dirac (Real.sqrt (r2/r1))) ∧
    ENNReal.ofReal (∫ x, x ∂(ENNReal.ofReal (r1^2/r2) •
      Measure.dirac (Real.sqrt (r2/r1)))) = alphaC ![r1,r2] := by
  have h1 : 0 < r1 := lt_of_lt_of_le h2 hle
  set x0 := Real.sqrt (r2 / r1) with hx0
  have hq : 0 < r2 / r1 := div_pos h2 h1
  have hx0pos : 0 < x0 := Real.sqrt_pos.mpr hq
  have hx0sq : x0 ^ 2 = r2 / r1 := Real.sq_sqrt hq.le
  have hx0le : x0 ≤ 1 := by
    rw [hx0, Real.sqrt_le_one]; exact (div_le_one h1).mpr hle
  set c := r1 ^ 2 / r2 with hc
  have hc0 : 0 ≤ c := by positivity
  set μ0 : Measure ℝ := ENNReal.ofReal c • Measure.dirac x0 with hμ0
  have hint : ∀ f : ℝ → ℝ, ∫ x, f x ∂μ0 = c * f x0 := by
    intro f
    rw [hμ0, integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hc0, smul_eq_mul]
  have hintg : ∀ f : ℝ → ℝ, Integrable f μ0 := by
    intro f
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have target : c * x0 = r1 * Real.sqrt r1 / Real.sqrt r2 := by
    have hs1 : Real.sqrt r1 ^ 2 = r1 := Real.sq_sqrt h1.le
    have hs2 : Real.sqrt r2 ^ 2 = r2 := Real.sq_sqrt h2.le
    have hsr2 : 0 < Real.sqrt r2 := Real.sqrt_pos.mpr h2
    have hsr1 : 0 < Real.sqrt r1 := Real.sqrt_pos.mpr h1
    rw [hx0, Real.sqrt_div' _ h1.le, hc]
    rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination r1 ^ 2 * hs2 - r1 * r2 * hs1
  have hfeas : continuousFeasible ![r1, r2] μ0 := by
    refine ⟨?_, ?_, hintg _, ?_⟩
    · simp [hμ0]
    · rw [hμ0, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Icc.compl]
      simp [Set.indicator, hx0pos.le, hx0le]
    · intro k
      refine ⟨hintg _, ?_⟩
      rw [hint]
      fin_cases k
      · simp only [Fin.zero_eta, Fin.isValue, Fin.val_zero, zero_add, mul_one,
          Matrix.cons_val_zero]
        rw [hx0sq, hc]; field_simp
      · simp only [Fin.mk_one, Fin.isValue, Fin.val_one, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        rw [show x0 ^ (2 * (1 + 1)) = (x0 ^ 2) ^ 2 by ring, hx0sq, hc]; field_simp
  have hval : ENNReal.ofReal (∫ x, x ∂μ0) = ENNReal.ofReal (r1 * Real.sqrt r1 / Real.sqrt r2) := by
    rw [hint, target]
  have hα : alphaC ![r1, r2] = ENNReal.ofReal (r1 * Real.sqrt r1 / Real.sqrt r2) := by
    apply le_antisymm
    · rw [← hval]; exact sInf_le ⟨μ0, hfeas, rfl⟩
    · apply le_sInf
      rintro v ⟨μ, ⟨hfin, hsupp, hI1, hmom⟩, rfl⟩
      apply ENNReal.ofReal_le_ofReal
      obtain ⟨hI2, hm2⟩ := hmom 0
      obtain ⟨hI4, hm4⟩ := hmom 1
      simp only [Fin.isValue, Fin.val_zero, zero_add, mul_one, Matrix.cons_val_zero] at hI2 hm2
      simp only [Fin.isValue, Fin.val_one, Matrix.cons_val_one, Matrix.cons_val_zero] at hI4 hm4
      -- pointwise inequality on [0,1]
      have hpt : ∀ᵐ x ∂μ, 0 ≤ (2 * x0 / 3) * x + x ^ (2 * (1 + 1)) / (3 * x0 ^ 2) - x ^ 2 := by
        have : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1 := by
          rw [ae_iff]; simpa [Set.compl_def] using hsupp
        filter_upwards [this] with x hx
        have hx0' : 0 ≤ x := hx.1
        have key : 0 ≤ x * (x - x0) ^ 2 * (x + 2 * x0) := by positivity
        have e : (2 * x0 / 3) * x + x ^ (2 * (1 + 1)) / (3 * x0 ^ 2) - x ^ 2 =
            x * (x - x0) ^ 2 * (x + 2 * x0) / (3 * x0 ^ 2) := by
          field_simp; ring
        rw [e]; positivity
      have hnn := integral_nonneg_of_ae hpt
      have hA : Integrable (fun x : ℝ => 2 * x0 / 3 * x) μ := hI1.const_mul _
      have hB : Integrable (fun x : ℝ => x ^ (2 * (1 + 1)) / (3 * x0 ^ 2)) μ := hI4.div_const _
      have hAB : Integrable (fun x : ℝ => 2 * x0 / 3 * x + x ^ (2 * (1 + 1)) / (3 * x0 ^ 2)) μ :=
        hA.add hB
      have hEq : ∫ x, (2 * x0 / 3 * x + x ^ (2 * (1 + 1)) / (3 * x0 ^ 2) - x ^ 2) ∂μ =
          2 * x0 / 3 * ∫ x, x ∂μ + r2 / (3 * x0 ^ 2) - r1 := by
        rw [integral_sub hAB hI2, integral_add hA hB, integral_const_mul, integral_div, hm2, hm4]
      rw [hEq] at hnn
      -- r1 ≤ (2 x0 / 3) ∫x + r2 / (3 x0²) = (2 x0/3) ∫ x + r1 / 3
      have e2 : r2 / (3 * x0 ^ 2) = r1 / 3 := by rw [hx0sq]; field_simp
      rw [e2] at hnn
      rw [← target]
      have : (2 * x0 / 3) * (c * x0) = 2 * r1 / 3 := by
        rw [show (2 * x0 / 3) * (c * x0) = 2 / 3 * c * x0 ^ 2 by ring, hx0sq, hc]
        field_simp
      nlinarith
  refine ⟨hα, hfeas, ?_⟩
  rw [hval, hα]
