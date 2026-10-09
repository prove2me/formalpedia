-- Prove2me | solution 1 for TroppMatrixConcentration.ch5_chernoff_mgf_cgf
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T01:35:13.423194+00:00
-- url     : https://prove2.me/submissions/eaee0d99-3b52-4d15-84f9-b6a2d8debb52

import Definitions.Def_TroppMatrixConcentration_ch5_chernoff_functions
import Theorems.Thm_TroppMatrixConcentration_ch3_lieb_integral_posDef
import Theorems.Thm_TroppMatrixConcentration_ch3_cgf_exp_log
import Theorems.Thm_TroppMatrixConcentration_ch8_log_operator_monotone
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
set_option autoImplicit false

namespace TroppMatrixConcentration
namespace Ch5ChernoffMgf

/-- Scalar chord bound: `exp (θ x) ≤ 1 + g x` on `[0, L]`. -/
lemma scalar_bound (L θ x : ℝ) (hL : 0 ≤ L) (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    Real.exp (θ * x) ≤ 1 + chernoffCgfCoefficient L θ * x := by
  unfold chernoffCgfCoefficient
  split_ifs with h
  · have : x = 0 := by linarith
    subst this; simp
  · have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm h)
    set t := x / L with ht
    have ht0 : 0 ≤ t := div_nonneg hx0 hL
    have ht1 : t ≤ 1 := (div_le_one hLp).mpr hxL
    have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (θ * L))
      (sub_nonneg.mpr ht1) ht0 (by ring)
    have hxe : x = t * L := by rw [ht]; field_simp
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    calc Real.exp (θ * x) = Real.exp (t * (θ * L)) := by rw [hxe]; ring_nf
      _ ≤ (1 - t) + t * Real.exp (θ * L) := hc
      _ = 1 + (Real.exp (θ * L) - 1) / L * x := by rw [hxe]; field_simp; ring

lemma spec_mem {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (L : ℝ)
    (hB : 0 ≤ lambdaMin A ∧ lambdaMax A ≤ L) : ∀ x ∈ spectrum ℝ A, 0 ≤ x ∧ x ≤ L := by
  intro x hx
  have hfin : (spectrum ℝ A).Finite := by
    rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  exact ⟨hB.1.trans (csInf_le hfin.bddBelow hx), (le_csSup hfin.bddAbove hx).trans hB.2⟩

lemma matrixExp_smul_eq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (s : ℝ) :
    matrixExp (s • A) = cfc (fun x => Real.exp (s * x)) A := by
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp
    (hA.smul (isSelfAdjoint_iff.mpr (star_trivial s))),
    ← cfc_comp_const_mul s Real.exp A (by fun_prop) hA.isSelfAdjoint]

lemma affine_eq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (c : ℝ) :
    (1 : Matrix (Fin d) (Fin d) ℂ) + c • A = cfc (fun x : ℝ => 1 + c * x) A := by
  rw [cfc_const_add 1 (fun x : ℝ => c * x) A (by fun_prop) hA.isSelfAdjoint,
    cfc_const_mul_id c A hA.isSelfAdjoint, map_one]

lemma pointwise {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (L θ : ℝ)
    (hL : 0 ≤ L) (hB : 0 ≤ lambdaMin A ∧ lambdaMax A ≤ L) :
    matrixExp (θ • A) ≤ 1 + chernoffCgfCoefficient L θ • A := by
  rw [matrixExp_smul_eq A hA, affine_eq A hA]
  refine cfc_mono (fun x hx => ?_) (by fun_prop) (by fun_prop)
  have := spec_mem A hA L hB x hx
  exact scalar_bound L θ x hL this.1 this.2

lemma norm_le {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (L : ℝ)
    (hL : 0 ≤ L) (hB : 0 ≤ lambdaMin A ∧ lambdaMax A ≤ L) : ‖A‖ ≤ L := by
  have h := norm_cfc_le (a := A) (f := fun x : ℝ => x) hL (fun x hx => by
    have := spec_mem A hA L hB x hx
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)
  rwa [cfc_id' ℝ A hA.isSelfAdjoint] at h

lemma norm_exp_le {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (L θ : ℝ) (hB : 0 ≤ lambdaMin A ∧ lambdaMax A ≤ L) :
    ‖matrixExp (θ • A)‖ ≤ Real.exp (|θ| * L) := by
  rw [matrixExp_smul_eq A hA]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x hx
  have := spec_mem A hA L hB x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc θ * x ≤ |θ * x| := le_abs_self _
    _ = |θ| * x := by rw [abs_mul, abs_of_nonneg this.1]
    _ ≤ |θ| * L := mul_le_mul_of_nonneg_left this.2 (abs_nonneg θ)

lemma nonneg {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (L : ℝ)
    (hB : 0 ≤ lambdaMin A ∧ lambdaMax A ≤ L) : (0 : Matrix (Fin d) (Fin d) ℂ) ≤ A := by
  have h : (0 : Matrix (Fin d) (Fin d) ℂ) ≤ cfc (fun x : ℝ => x) A :=
    cfc_nonneg (fun x hx => (spec_mem A hA L hB x hx).1)
  rwa [cfc_id' ℝ A hA.isSelfAdjoint] at h

lemma one_add_le_exp {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) (hB : B.IsHermitian) :
    1 + B ≤ matrixExp B := by
  have e1 : (1 : Matrix (Fin d) (Fin d) ℂ) + B = cfc (fun x : ℝ => 1 + x) B := by
    rw [cfc_const_add 1 (fun x : ℝ => x) B (by fun_prop) hB.isSelfAdjoint,
      cfc_id' ℝ B hB.isSelfAdjoint, map_one]
  rw [e1, matrixExp, ← CFC.real_exp_eq_normedSpace_exp hB.isSelfAdjoint]
  refine cfc_mono (fun x _ => ?_) (by fun_prop) (by fun_prop)
  linarith [Real.add_one_le_exp x]

lemma log_one_add_le {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) (hpd : (1 + B).PosDef) :
    matrixLog (1 + B) ≤ B := by
  have hH : (1 + B).IsHermitian := hpd.isHermitian
  have hspec : ∀ y ∈ spectrum ℝ (1 + B), 0 < y := by
    rw [hH.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    exact hpd.eigenvalues_pos i
  have e2 : cfc (fun y : ℝ => y - 1) (1 + B) = B := by
    rw [cfc_sub (fun y : ℝ => y) (fun _ => (1 : ℝ)) (1 + B) (by fun_prop) (by fun_prop),
      cfc_id' ℝ (1 + B) hH.isSelfAdjoint, cfc_const_one ℝ (1 + B) hH.isSelfAdjoint]
    abel
  calc matrixLog (1 + B) ≤ cfc (fun y : ℝ => y - 1) (1 + B) := by
        unfold matrixLog
        refine cfc_mono (fun y hy => Real.log_le_sub_one_of_pos (hspec y hy)) ?_ (by fun_prop)
        exact Real.continuousOn_log.mono (fun y hy => (hspec y hy).ne')
    _ = B := e2

end Ch5ChernoffMgf
end TroppMatrixConcentration

open TroppMatrixConcentration

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (X : Ω → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hMeas : Measurable X) (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hBound : ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (X ω) ∧ lambdaMax (X ω) ≤ L)
    (θ : ℝ) :
    loewnerLE (∫ ω, matrixExp (θ • X ω) ∂μ)
      (matrixExp (chernoffCgfCoefficient L θ • (∫ ω, X ω ∂μ))) ∧
    loewnerLE (matrixLog (∫ ω, matrixExp (θ • X ω) ∂μ))
      (chernoffCgfCoefficient L θ • (∫ ω, X ω ∂μ)) := by
  set g := chernoffCgfCoefficient L θ with hg
  have hXae : AEStronglyMeasurable X μ := hMeas.aestronglyMeasurable
  have hXint : Integrable X μ := Integrable.of_bound hXae L (by
    filter_upwards [hHerm, hBound] with ω h1 h2
    exact Ch5ChernoffMgf.norm_le (X ω) h1 L hL h2)
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hcont : Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => matrixExp (θ • A)) := by
    dsimp [matrixExp]
    fun_prop
  have hEint : Integrable (fun ω => matrixExp (θ • X ω)) μ :=
    Integrable.of_bound (hcont.comp_aestronglyMeasurable hXae) (Real.exp (|θ| * L)) (by
      filter_upwards [hHerm, hBound] with ω h1 h2
      exact Ch5ChernoffMgf.norm_exp_le (X ω) h1 L θ h2)
  -- pointwise transfer rule and integration
  have hdiff : ∀ᵐ ω ∂μ, (0 : Matrix (Fin d) (Fin d) ℂ) ≤
      ((1 : Matrix (Fin d) (Fin d) ℂ) + g • X ω) - matrixExp (θ • X ω) := by
    filter_upwards [hHerm, hBound] with ω h1 h2
    exact sub_nonneg.mpr (Ch5ChernoffMgf.pointwise (X ω) h1 L θ hL h2)
  have h0 := integral_nonneg_of_ae hdiff
  have hAint : Integrable (fun ω => (1 : Matrix (Fin d) (Fin d) ℂ) + g • X ω) μ :=
    (integrable_const _).add (hXint.smul g)
  have hI : ∫ ω, ((1 : Matrix (Fin d) (Fin d) ℂ) + g • X ω) - matrixExp (θ • X ω) ∂μ =
      (1 + g • ∫ ω, X ω ∂μ) - ∫ ω, matrixExp (θ • X ω) ∂μ := by
    rw [integral_sub hAint hEint, integral_add (f := fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) (g := fun ω => g • X ω)
        (integrable_const _) (hXint.smul g),
      integral_const, integral_smul]
    simp
  rw [hI] at h0
  have hE_le : (∫ ω, matrixExp (θ • X ω) ∂μ) ≤ 1 + g • ∫ ω, X ω ∂μ := sub_nonneg.mp h0
  -- the mean is Hermitian
  have hM0 : (0 : Matrix (Fin d) (Fin d) ℂ) ≤ ∫ ω, X ω ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hHerm, hBound] with ω h1 h2
    exact Ch5ChernoffMgf.nonneg (X ω) h1 L h2
  have hMherm : (∫ ω, X ω ∂μ).IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hM0).isHermitian
  have hBherm : (g • ∫ ω, X ω ∂μ).IsHermitian :=
    hMherm.smul (isSelfAdjoint_iff.mpr (star_trivial g))
  have h1B := Ch5ChernoffMgf.one_add_le_exp _ hBherm
  refine ⟨Matrix.le_iff.mp (hE_le.trans h1B), ?_⟩
  -- part (2)
  have hEpd : (∫ ω, matrixExp (θ • X ω) ∂μ).PosDef := by
    apply ch3_lieb_integral_posDef μ _ hEint
    filter_upwards [hHerm] with ω h1
    exact (ch3_cgf_exp_log _ (h1.smul (isSelfAdjoint_iff.mpr (star_trivial θ)))).1
  have hD := Matrix.le_iff.mp hE_le
  have h1Bpd : ((1 : Matrix (Fin d) (Fin d) ℂ) + g • ∫ ω, X ω ∂μ).PosDef := by
    have := hEpd.add_posSemidef hD
    rwa [add_sub_cancel] at this
  have hlog1 := ch8_log_operator_monotone _ _ hEpd h1Bpd hD
  have hlog2 := Ch5ChernoffMgf.log_one_add_le _ h1Bpd
  exact Matrix.le_iff.mp ((Matrix.le_iff.mpr hlog1).trans hlog2)
