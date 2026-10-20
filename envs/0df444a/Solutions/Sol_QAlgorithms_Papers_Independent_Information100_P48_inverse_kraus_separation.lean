-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P48.inverse_kraus_separation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:08:17.519523+00:00
-- url     : https://prove2.me/submissions/12a348fb-7d34-42fa-baf1-513a852f1c79

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

theorem g52c_psd_conj (K X : QOp) (hX : X.PosSemidef) : (K * X * Kᴴ).PosSemidef :=
  hX.mul_mul_conjTranspose_same K

end

end QAlgorithms.Papers.Independent.Information100.P48

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P48 in
open scoped Matrix ComplexConjugate ComplexOrder in
theorem solution (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (∀ (s t : Bool) (e : Bool),
      (dilation g)ᴴ (s, e) (t, false) =
        (Matrix.kronecker (1 : QOp) pauliZ * dilation g) (s, e) (t, false)) ∧
    (∀ rho : QOp,
      cross (dilation g)ᴴ (dilation g)ᴴ false rho = adc g rho ∧
      cross (dilation g) (dilation g)ᴴ false rho =
        k0 g * rho * (k0 g)ᴴ - k1 g * rho * (k1 g)ᴴ ∧
      cross (dilation g)ᴴ (dilation g) false rho =
        k0 g * rho * (k0 g)ᴴ - k1 g * rho * (k1 g)ᴴ ∧
      sharedADC g false rho = k0 g * rho * (k0 g)ᴴ ∧
      sharedADC g true rho = k1 g * rho * (k1 g)ᴴ) ∧
    (∀ rho : QOp, IsDensityMatrix rho → ∀ minus : Bool,
      (sharedADC g minus rho).trace.re =
        (if minus then g * (rho true true).re else 1 - g * (rho true true).re) ∧
      (0 < (sharedADC g minus rho).trace.re →
        IsDensityMatrix (normalize (sharedADC g minus rho)))) := by
  obtain ⟨u, hu0, rfl⟩ : ∃ u : ℝ, 0 ≤ u ∧ g = u ^ 2 := ⟨Real.sqrt g, Real.sqrt_nonneg _, (Real.sq_sqrt hg0).symm⟩
  have hu1 : u ≤ 1 := by nlinarith
  have hsin : Real.sin (Real.arcsin u) = u := Real.sin_arcsin (by linarith) hu1
  have hform : ∀ rho : QOp, sharedADC (u ^ 2) false rho = k0 (u ^ 2) * rho * (k0 (u ^ 2))ᴴ ∧
      sharedADC (u ^ 2) true rho = k1 (u ^ 2) * rho * (k1 (u ^ 2))ᴴ := by
    intro rho
    constructor <;> ext a b <;> cases a <;> cases b <;>
      simp [cross, traceEnv, cleanInput, dilation, adcUnitary, pairMatrix, pairIndex, outcomeSign,
      Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.single_apply, Matrix.conjTranspose_apply, principalAngle, Real.cos_arcsin,
      ← Complex.ofReal_sin, ← Complex.ofReal_cos, Complex.conj_ofReal, Real.sqrt_sq hu0, hsin,
      adc, k0, k1, Matrix.diagonal_apply, sharedADC, branch, selectedOperator, Matrix.one_apply, pauliZ] <;> ring1
  refine ⟨?_, fun rho => ⟨?_, ?_, ?_, (hform rho).1, (hform rho).2⟩, ?_⟩
  · intro s t e
    cases s <;> cases t <;> cases e <;> simp [cross, traceEnv, cleanInput, dilation, adcUnitary, pairMatrix, pairIndex, outcomeSign,
      Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.single_apply, Matrix.conjTranspose_apply, principalAngle, Real.cos_arcsin,
      ← Complex.ofReal_sin, ← Complex.ofReal_cos, Complex.conj_ofReal, Real.sqrt_sq hu0, hsin,
      adc, k0, k1, Matrix.diagonal_apply, sharedADC, branch, selectedOperator, Matrix.one_apply, pauliZ]
  · ext a b; cases a <;> cases b <;> simp [cross, traceEnv, cleanInput, dilation, adcUnitary, pairMatrix, pairIndex, outcomeSign,
      Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.single_apply, Matrix.conjTranspose_apply, principalAngle, Real.cos_arcsin,
      ← Complex.ofReal_sin, ← Complex.ofReal_cos, Complex.conj_ofReal, Real.sqrt_sq hu0, hsin,
      adc, k0, k1, Matrix.diagonal_apply, sharedADC, branch, selectedOperator, Matrix.one_apply, pauliZ] <;> ring1
  · ext a b; cases a <;> cases b <;> simp [cross, traceEnv, cleanInput, dilation, adcUnitary, pairMatrix, pairIndex, outcomeSign,
      Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.single_apply, Matrix.conjTranspose_apply, principalAngle, Real.cos_arcsin,
      ← Complex.ofReal_sin, ← Complex.ofReal_cos, Complex.conj_ofReal, Real.sqrt_sq hu0, hsin,
      adc, k0, k1, Matrix.diagonal_apply, sharedADC, branch, selectedOperator, Matrix.one_apply, pauliZ] <;> ring1
  · ext a b; cases a <;> cases b <;> simp [cross, traceEnv, cleanInput, dilation, adcUnitary, pairMatrix, pairIndex, outcomeSign,
      Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.single_apply, Matrix.conjTranspose_apply, principalAngle, Real.cos_arcsin,
      ← Complex.ofReal_sin, ← Complex.ofReal_cos, Complex.conj_ofReal, Real.sqrt_sq hu0, hsin,
      adc, k0, k1, Matrix.diagonal_apply, sharedADC, branch, selectedOperator, Matrix.one_apply, pauliZ] <;> ring1
  · intro rho hrho minus
    have htr : (rho false false).re + (rho true true).re = 1 := by
      have := congrArg Complex.re hrho.2
      simp [Matrix.trace, Fintype.sum_bool] at this
      linarith
    have hpsd : (sharedADC (u ^ 2) minus rho).PosSemidef := by
      cases minus
      · rw [(hform rho).1]; exact g52c_psd_conj _ _ hrho.1
      · rw [(hform rho).2]; exact g52c_psd_conj _ _ hrho.1
    have htrace : (sharedADC (u ^ 2) minus rho).trace.re =
        (if minus then u ^ 2 * (rho true true).re else 1 - u ^ 2 * (rho true true).re) := by
      have hs2 : Real.sqrt (1 - u ^ 2) * Real.sqrt (1 - u ^ 2) = 1 - u ^ 2 :=
        Real.mul_self_sqrt (by nlinarith)
      cases minus
      · rw [(hform rho).1]
        simp [Matrix.trace, Fintype.sum_bool, k0, Matrix.mul_apply, Matrix.diagonal_apply,
          Matrix.conjTranspose_apply]
        have h3 : Real.sqrt (1 - u ^ 2) * Real.sqrt (1 - u ^ 2) * (rho true true).re =
            (1 - u ^ 2) * (rho true true).re := by rw [hs2]
        nlinarith [h3, htr]
      · rw [(hform rho).2]
        simp [Matrix.trace, Fintype.sum_bool, k1, Matrix.mul_apply, Matrix.conjTranspose_apply]
        have h3 : (Real.sqrt (u ^ 2)) = u := Real.sqrt_sq hu0
        simp [h3]
        ring
    refine ⟨htrace, fun hpos => ?_⟩
    have hre : (sharedADC (u ^ 2) minus rho).trace = ((sharedADC (u ^ 2) minus rho).trace.re : ℂ) := by
      apply Complex.ext
      · simp
      · simp only [Complex.ofReal_im]
        exact ((Complex.nonneg_iff.mp hpsd.trace_nonneg).2).symm
    set r := (sharedADC (u ^ 2) minus rho).trace.re with hr
    have hne : (r : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    constructor
    · simp only [QAlgorithms.Papers.Independent.Information100.P48.normalize]
      rw [← hr, ← Complex.ofReal_inv]
      exact hpsd.smul (Complex.zero_le_real.mpr (inv_pos.mpr hpos).le)
    · simp only [QAlgorithms.Papers.Independent.Information100.P48.normalize, Matrix.trace_smul, smul_eq_mul]
      rw [← hr, hre]
      field_simp
