-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P48.independent_adc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:07:35.310985+00:00
-- url     : https://prove2.me/submissions/649a9f37-5db1-470f-964a-28a902c119dc

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

theorem g52c_indep_apply (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (X : QOp) (a b : Bool) :
    independentADC g false X a b =
      ((if a then ((Real.sqrt (1 - g) : ℝ) : ℂ) else 1) * (if b then ((Real.sqrt (1 - g) : ℝ) : ℂ) else 1)) * X a b
      + (if a = false ∧ b = false then ((g / 2 : ℝ) : ℂ) * X true true else 0) := by
  have hs1 : Real.sqrt g ≤ 1 := by rw [Real.sqrt_le_one]; exact hg1
  have hs0 : -1 ≤ Real.sqrt g := by linarith [Real.sqrt_nonneg g]
  have hsin : Real.sin (Real.arcsin (Real.sqrt g)) = Real.sqrt g := Real.sin_arcsin hs0 hs1
  have hc : ((Real.sqrt g : ℝ) : ℂ) ^ 2 = (g : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hg0]
  cases a <;> cases b <;>
  simp [independentADC, branch, cross, selectedOperator, traceEnv, cleanInput, embed0, embed1,
    dilation, adcUnitary,
    pairMatrix, pairIndex, outcomeSign, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.single_apply, Matrix.conjTranspose_apply, principalAngle,
    Real.cos_arcsin, ← Complex.ofReal_sin, ← Complex.ofReal_cos, Complex.conj_ofReal, Real.sq_sqrt hg0,
    hsin, hc]
  all_goals first | ring1 | linear_combination (X true true * (1/2)) * hc |
    linear_combination (X true true) * hc | linear_combination (X true true * (1/2 : ℂ)) * hc

theorem g52c_indep_true_apply (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (X : QOp) (a b : Bool) :
    independentADC g true X a b = if a = false ∧ b = false then ((g / 2 : ℝ) : ℂ) * X true true else 0 := by
  have hs1 : Real.sqrt g ≤ 1 := by rw [Real.sqrt_le_one]; exact hg1
  have hs0 : -1 ≤ Real.sqrt g := by linarith [Real.sqrt_nonneg g]
  have hsin : Real.sin (Real.arcsin (Real.sqrt g)) = Real.sqrt g := Real.sin_arcsin hs0 hs1
  have hc : ((Real.sqrt g : ℝ) : ℂ) ^ 2 = (g : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hg0]
  cases a <;> cases b <;>
  simp [independentADC, branch, cross, selectedOperator, traceEnv, cleanInput, embed0, embed1,
    dilation, adcUnitary,
    pairMatrix, pairIndex, outcomeSign, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.single_apply, Matrix.conjTranspose_apply, principalAngle,
    Real.cos_arcsin, ← Complex.ofReal_sin, ← Complex.ofReal_cos, Complex.conj_ofReal, Real.sq_sqrt hg0,
    hsin, hc]
  all_goals first | ring1 | linear_combination (X true true * (1/2)) * hc |
    linear_combination (X true true) * hc | linear_combination (X true true * (1/2 : ℂ)) * hc


theorem g52c_psd_conj (K X : QOp) (hX : X.PosSemidef) : (K * X * Kᴴ).PosSemidef :=
  hX.mul_mul_conjTranspose_same K

end

end QAlgorithms.Papers.Independent.Information100.P48

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P48 in
open scoped Matrix ComplexConjugate ComplexOrder in
theorem solution (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    interference (dilation g) false = k0 g ∧
    (∀ rho : QOp,
      independentADC g false rho = k0 g * rho * (k0 g)ᴴ +
        (1 / 2 : ℂ) • (k1 g * rho * (k1 g)ᴴ) ∧
      independentADC g true rho = (1 / 2 : ℂ) • (k1 g * rho * (k1 g)ᴴ)) ∧
    (∀ rho : QOp, IsDensityMatrix rho → ∀ minus : Bool,
      (independentADC g minus rho).trace.re =
        (if minus then g / 2 * (rho true true).re else 1 - g / 2 * (rho true true).re) ∧
      (0 < (independentADC g minus rho).trace.re →
        IsDensityMatrix (normalize (independentADC g minus rho)))) ∧
    (∀ (A B : QOp) (a b minus : Bool),
      rawJoint (independentADC g minus) A B a b =
        (1 / 2 : ℝ) * (projector B b * independentADC g minus (projector A a)).trace.re) := by
  have hsg : ((Real.sqrt g : ℝ) : ℂ) * ((Real.sqrt g : ℝ) : ℂ) = (g : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hg0]
  have hform : ∀ rho : QOp,
      independentADC g false rho = k0 g * rho * (k0 g)ᴴ + (1 / 2 : ℂ) • (k1 g * rho * (k1 g)ᴴ) ∧
      independentADC g true rho = (1 / 2 : ℂ) • (k1 g * rho * (k1 g)ᴴ) := by
    intro rho
    constructor
    · ext a b
      rw [g52c_indep_apply g hg0 hg1]
      cases a <;> cases b <;>
        simp [k0, k1, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply] <;>
        first | ring1 | linear_combination (-(1/2 : ℂ) * rho true true) * hsg
    · ext a b
      rw [g52c_indep_true_apply g hg0 hg1]
      cases a <;> cases b <;>
        simp [k0, k1, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply] <;>
        first | ring1 | linear_combination (-(1/2 : ℂ) * rho true true) * hsg
  refine ⟨?_, hform, ?_, fun A B a b minus => rfl⟩
  · ext s t
    cases s <;> cases t <;>
      simp [interference, dilation, adcUnitary, pairMatrix, pairIndex, k0, principalAngle,
        Real.cos_arcsin, Real.sq_sqrt hg0, Matrix.diagonal_apply]
  · intro rho hrho minus
    have htr : (rho false false).re + (rho true true).re = 1 := by
      have := congrArg Complex.re hrho.2
      simp [Matrix.trace, Fintype.sum_bool] at this
      linarith
    have hpsd : (independentADC g minus rho).PosSemidef := by
      cases minus
      · rw [(hform rho).1]
        exact (g52c_psd_conj _ _ hrho.1).add ((g52c_psd_conj _ _ hrho.1).smul (by rw [Complex.nonneg_iff]; norm_num))
      · rw [(hform rho).2]
        exact (g52c_psd_conj _ _ hrho.1).smul (by rw [Complex.nonneg_iff]; norm_num)
    have htrace : (independentADC g minus rho).trace.re =
        (if minus then g / 2 * (rho true true).re else 1 - g / 2 * (rho true true).re) := by
      have hs2 : Real.sqrt (1 - g) * Real.sqrt (1 - g) = 1 - g := Real.mul_self_sqrt (by linarith)
      cases minus
      · simp only [Matrix.trace, Matrix.diag, Fintype.sum_bool, g52c_indep_apply g hg0 hg1]
        simp
        have h3 : Real.sqrt (1 - g) * Real.sqrt (1 - g) * (rho true true).re =
            (1 - g) * (rho true true).re := by rw [hs2]
        linarith
      · simp [Matrix.trace, Matrix.diag, Fintype.sum_bool, g52c_indep_true_apply g hg0 hg1]
        try ring
    refine ⟨htrace, fun hpos => ?_⟩
    have hre : (independentADC g minus rho).trace = ((independentADC g minus rho).trace.re : ℂ) := by
      apply Complex.ext
      · simp
      · simp only [Complex.ofReal_im]
        exact ((Complex.nonneg_iff.mp hpsd.trace_nonneg).2).symm
    set r := (independentADC g minus rho).trace.re with hr
    have hne : (r : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    constructor
    · simp only [QAlgorithms.Papers.Independent.Information100.P48.normalize]
      rw [← hr, ← Complex.ofReal_inv]
      exact hpsd.smul (Complex.zero_le_real.mpr (inv_pos.mpr hpos).le)
    · simp only [QAlgorithms.Papers.Independent.Information100.P48.normalize, Matrix.trace_smul, smul_eq_mul]
      rw [← hr, hre]
      field_simp
