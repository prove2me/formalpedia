-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.covariantZeroFrequency
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:31:12.272972+00:00
-- url     : https://prove2.me/submissions/5e48c052-ac3e-41bf-9e47-d7dcb076fd72

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

theorem g52c_timeEvolution_unit {d : ℕ} (E : Fin d → ℝ) (t : ℝ) (i j : Fin d) :
    timeEvolution E t (matrixUnit i j) =
      Complex.exp (-Complex.I * (t : ℂ) * ((E i - E j : ℝ) : ℂ)) • matrixUnit i j := by
  ext a b
  simp only [timeEvolution, matrixUnit, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h; simp
  · simp [h]

theorem g52c_exp_neg_one (x : ℝ) (hx : x ≠ 0) :
    Complex.exp (-Complex.I * ((Real.pi / x : ℝ) : ℂ) * (x : ℂ)) = -1 := by
  have : -Complex.I * ((Real.pi / x : ℝ) : ℂ) * (x : ℂ) = -(Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num

end

end QAlgorithms.Papers.Independent.Information100.P44

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44 in
open scoped ComplexConjugate ComplexOrder Matrix in
theorem solution {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ)
    (Phi : Map d) (hlin : IsComplexLinear Phi) (hcov : IsCovariant E Phi) :
    (∀ i j, E i ≠ E j → ∀ r, Phi (matrixUnit i j) r r = 0) ∧
    (∀ r s, E r ≠ E s → ∀ i, Phi (matrixUnit i i) r s = 0) := by
  constructor
  · intro i j hij r
    have hx : E i - E j ≠ 0 := sub_ne_zero.mpr hij
    have h := congrFun (congrFun (hcov (Real.pi / (E i - E j)) (matrixUnit i j)) r) r
    rw [g52c_timeEvolution_unit, hlin.2, g52c_exp_neg_one _ hx] at h
    simp only [Matrix.smul_apply, smul_eq_mul, timeEvolution, sub_self, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, one_mul] at h
    have : (2 : ℂ) * Phi (matrixUnit i j) r r = 0 := by linear_combination -h
    simpa using this
  · intro r s hrs i
    have hx : E r - E s ≠ 0 := sub_ne_zero.mpr hrs
    have h := congrFun (congrFun (hcov (Real.pi / (E r - E s)) (matrixUnit i i)) r) s
    rw [g52c_timeEvolution_unit] at h
    simp only [sub_self, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul] at h
    simp only [timeEvolution] at h
    rw [g52c_exp_neg_one _ hx] at h
    have : (2 : ℂ) * Phi (matrixUnit i i) r s = 0 := by linear_combination h
    simpa using this
