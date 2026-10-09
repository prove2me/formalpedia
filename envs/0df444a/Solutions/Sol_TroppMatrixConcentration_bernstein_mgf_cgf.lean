-- Prove2me | solution 1 for TroppMatrixConcentration.bernstein_mgf_cgf
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T01:35:14.259434+00:00
-- url     : https://prove2.me/submissions/c613079b-d171-4c63-8a94-fc33f8d10239

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation
import Theorems.Thm_TroppMatrixConcentration_ch3_lieb_integral_posDef
import Theorems.Thm_TroppMatrixConcentration_ch3_cgf_exp_log
import Theorems.Thm_TroppMatrixConcentration_ch8_log_operator_monotone
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TroppMatrixConcentration
namespace BernsteinMGF

/-- Auxiliary function `g(u) = u²/2 - (1 - u/3)(eᵘ - 1 - u)`. -/
noncomputable def gFun (u : ℝ) : ℝ := u ^ 2 / 2 - (1 - u / 3) * (Real.exp u - 1 - u)

/-- Its derivative `h = g'`. -/
noncomputable def hFun (u : ℝ) : ℝ := u + (Real.exp u - 1 - u) / 3 - (1 - u / 3) * (Real.exp u - 1)

lemma hasDerivAt_hFun (u : ℝ) : HasDerivAt hFun ((1 - Real.exp u * (1 - u)) / 3) u := by
  have h1 := (((Real.hasDerivAt_exp u).sub_const 1).sub (hasDerivAt_id u)).div_const 3
  have h2 := ((hasDerivAt_id u).div_const 3).const_sub 1
  have h3 := h2.mul ((Real.hasDerivAt_exp u).sub_const 1)
  have h4 := ((hasDerivAt_id u).add h1).sub h3
  refine (h4.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · simp; ring
  · simp [hFun]

lemma hasDerivAt_gFun (u : ℝ) : HasDerivAt gFun (hFun u) u := by
  have h1 := ((Real.hasDerivAt_exp u).sub_const 1).sub (hasDerivAt_id u)
  have h2 := ((hasDerivAt_id u).div_const 3).const_sub 1
  have h4 := ((hasDerivAt_pow 2 u).div_const 2).sub (h2.mul h1)
  refine (h4.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · simp [hFun]; ring
  · simp [gFun]

lemma hFun_mono : Monotone hFun := by
  apply monotone_of_deriv_nonneg (fun u => (hasDerivAt_hFun u).differentiableAt)
  intro u
  rw [(hasDerivAt_hFun u).deriv]
  have h1 := Real.add_one_le_exp (-u)
  have h2 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos u
  apply div_nonneg _ (by norm_num)
  nlinarith

lemma gFun_nonneg (u : ℝ) : 0 ≤ gFun u := by
  have hdiff : Differentiable ℝ gFun := fun u => (hasDerivAt_gFun u).differentiableAt
  have g0 : gFun 0 = 0 := by simp [gFun]
  have h0 : hFun 0 = 0 := by simp [hFun]
  rcases le_total u 0 with hu | hu
  · have hanti : AntitoneOn gFun (Set.Iic 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic 0) hdiff.continuous.continuousOn
        hdiff.differentiableOn
      intro x hx
      rw [interior_Iic] at hx
      rw [(hasDerivAt_gFun x).deriv]
      have := hFun_mono (le_of_lt (Set.mem_Iio.mp hx))
      linarith
    have := hanti (Set.mem_Iic.mpr hu) (Set.mem_Iic.mpr le_rfl) hu
    linarith
  · have hmono : MonotoneOn gFun (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
        hdiff.differentiableOn
      intro x hx
      rw [interior_Ici] at hx
      rw [(hasDerivAt_gFun x).deriv]
      have := hFun_mono (le_of_lt (Set.mem_Ioi.mp hx))
      linarith
    have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
    linarith

/-- The scalar Bernstein mgf bound: for `x ≤ L`, `e^{θx} ≤ 1 + θx + c x²`. -/
lemma scalar_bound {L θ x : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3) (hx : x ≤ L) :
    Real.exp (θ * x) ≤ 1 + θ * x + (θ ^ 2 / 2) / (1 - θ * L / 3) * x ^ 2 := by
  have hux : θ * x ≤ θ * L := mul_le_mul_of_nonneg_left hx hθ.le
  have hpos : 0 < 1 - θ * L / 3 := by linarith
  have hpos' : 0 < 1 - θ * x / 3 := by linarith
  have hg := gFun_nonneg (θ * x)
  unfold gFun at hg
  have h1 : Real.exp (θ * x) - 1 - θ * x ≤ ((θ * x) ^ 2 / 2) / (1 - θ * x / 3) := by
    rw [le_div_iff₀ hpos']; nlinarith
  have h2 : ((θ * x) ^ 2 / 2) / (1 - θ * x / 3) ≤ ((θ * x) ^ 2 / 2) / (1 - θ * L / 3) :=
    div_le_div_of_nonneg_left (by positivity) hpos (by linarith)
  have h3 : (θ ^ 2 / 2) / (1 - θ * L / 3) * x ^ 2 = ((θ * x) ^ 2 / 2) / (1 - θ * L / 3) := by
    ring
  linarith

variable {d : ℕ}

lemma spec_le (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) {L : ℝ}
    (hb : lambdaMax A ≤ L) : ∀ x ∈ spectrum ℝ A, x ≤ L := by
  intro x hx
  have hfin : (spectrum ℝ A).Finite := by
    rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  exact (le_csSup hfin.bddAbove hx).trans hb

lemma matrixExp_smul_eq (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (s : ℝ) :
    matrixExp (s • A) = cfc (fun x => Real.exp (s * x)) A := by
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp (hA.smul (isSelfAdjoint_iff.mpr (star_trivial s))),
    ← cfc_comp_const_mul s Real.exp A (by fun_prop) hA.isSelfAdjoint]

lemma quad_eq (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (θ c : ℝ) :
    1 + θ • A + c • A ^ 2 = cfc (fun x => 1 + θ * x + c * x ^ 2) A := by
  have e1 := cfc_add A (fun x => 1 + θ * x) (fun x => c * x ^ 2)
  have e2 := cfc_const_add 1 (fun x => θ * x) A
  rw [e1, e2, cfc_const_mul_id θ A, cfc_const_mul c (fun x : ℝ => x ^ 2) A,
    cfc_pow_id A 2 hA.isSelfAdjoint, map_one]

lemma exp_le_quad (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) {θ c : ℝ}
    (hb : ∀ x ∈ spectrum ℝ A, Real.exp (θ * x) ≤ 1 + θ * x + c * x ^ 2) :
    matrixExp (θ • A) ≤ 1 + θ • A + c • A ^ 2 := by
  rw [matrixExp_smul_eq A hA θ, quad_eq A hA θ c]
  exact cfc_mono hb

lemma one_add_le_exp (B : Matrix (Fin d) (Fin d) ℂ) (hB : B.IsHermitian) :
    1 + B ≤ matrixExp B := by
  have e1 : 1 + B = cfc (fun x : ℝ => 1 + x) B := by
    rw [cfc_const_add (1 : ℝ) (fun x : ℝ => x) B, cfc_id' ℝ B hB.isSelfAdjoint, map_one]
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp hB, e1]
  exact cfc_mono (fun x _ => by linarith [Real.add_one_le_exp x])

end BernsteinMGF
end TroppMatrixConcentration

open TroppMatrixConcentration TroppMatrixConcentration.BernsteinMGF

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (X : Ω → Matrix (Fin d) (Fin d) ℂ) (L θ : ℝ)
    (hL : 0 < L) (hθ : 0 < θ) (hθL : θ < 3 / L)
    (hMeas : Measurable X) (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hL2 : MemLp X 2 μ) (hMean : (∫ ω, X ω ∂μ) = 0)
    (hBound : ∀ᵐ ω ∂μ, lambdaMax (X ω) ≤ L) :
    loewnerLE (∫ ω, matrixExp (θ • X ω) ∂μ)
      (matrixExp (((θ ^ 2 / 2) / (1 - θ * L / 3)) • (∫ ω, X ω ^ 2 ∂μ))) ∧
    loewnerLE (matrixLog (∫ ω, matrixExp (θ • X ω) ∂μ))
      (((θ ^ 2 / 2) / (1 - θ * L / 3)) • (∫ ω, X ω ^ 2 ∂μ)) := by
  have hθL' : θ * L < 3 := (lt_div_iff₀ hL).mp hθL
  set c := (θ ^ 2 / 2) / (1 - θ * L / 3) with hc
  -- integrability
  have hXint : Integrable X μ := hL2.integrable one_le_two
  have hX2int : Integrable (fun ω => X ω ^ 2) μ := by
    refine Integrable.mono' (hL2.integrable_norm_pow two_ne_zero) ?_
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact (continuous_pow 2).comp_aestronglyMeasurable hL2.1
    · rw [sq, sq]
      exact Matrix.l2_opNorm_mul _ _
  have hEcont : Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => matrixExp (θ • A)) := by
    let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
      NormedAlgebra.restrictScalars ℚ ℂ _
    dsimp [matrixExp]
    fun_prop
  have hEint : Integrable (fun ω => matrixExp (θ • X ω)) μ := by
    refine Integrable.of_bound (hEcont.comp_aestronglyMeasurable hMeas.aestronglyMeasurable)
      (Real.exp (θ * L)) ?_
    filter_upwards [hHerm, hBound] with ω hH hB
    rw [matrixExp_smul_eq _ hH]
    apply norm_cfc_le (Real.exp_pos _).le
    intro x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (spec_le _ hH hB x hx) hθ.le)
  have hXθ : Integrable (fun ω => θ • X ω) μ := hXint.smul θ
  have hX2c : Integrable (fun ω => c • X ω ^ 2) μ := hX2int.smul c
  have hlin : Integrable (fun ω => (1 : Matrix (Fin d) (Fin d) ℂ) + θ • X ω) μ :=
    (integrable_const 1).add hXθ
  have hQint : Integrable (fun ω => (1 : Matrix (Fin d) (Fin d) ℂ) + θ • X ω + c • X ω ^ 2) μ :=
    hlin.add hX2c
  have hpt : ∀ᵐ ω ∂μ, matrixExp (θ • X ω) ≤ 1 + θ • X ω + c • X ω ^ 2 := by
    filter_upwards [hHerm, hBound] with ω hH hB
    exact exp_le_quad _ hH (fun x hx => scalar_bound hθ hθL' (spec_le _ hH hB x hx))
  have hI1 : ∫ ω, matrixExp (θ • X ω) ∂μ ≤ 1 + c • ∫ ω, X ω ^ 2 ∂μ := by
    have h := integral_mono_ae hEint hQint hpt
    rw [integral_add hlin hX2c, integral_add (integrable_const 1) hXθ,
      integral_const, integral_smul, integral_smul, hMean] at h
    simpa using h
  -- the second moment is positive semidefinite
  have hS : (0 : Matrix (Fin d) (Fin d) ℂ) ≤ ∫ ω, X ω ^ 2 ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hHerm] with ω hH
    have : X ω ^ 2 = Matrix.conjTranspose (X ω) * X ω := by rw [hH.eq, sq]
    rw [Pi.zero_apply, this]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).nonneg
  set S := ∫ ω, X ω ^ 2 ∂μ with hSdef
  have hSH : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hS).isHermitian
  have hBH : (c • S).IsHermitian := hSH.smul (isSelfAdjoint_iff.mpr (star_trivial c))
  have h1 : ∫ ω, matrixExp (θ • X ω) ∂μ ≤ matrixExp (c • S) :=
    hI1.trans (one_add_le_exp _ hBH)
  refine ⟨Matrix.le_iff.mp h1, ?_⟩
  have hMPD : (∫ ω, matrixExp (θ • X ω) ∂μ).PosDef := by
    apply ch3_lieb_integral_posDef μ _ hEint
    filter_upwards [hHerm] with ω hH
    exact (ch3_cgf_exp_log _ (hH.smul (isSelfAdjoint_iff.mpr (star_trivial θ)))).1
  obtain ⟨hEPD, hlog⟩ := ch3_cgf_exp_log (c • S) hBH
  have h2 := ch8_log_operator_monotone _ _ hMPD hEPD (Matrix.le_iff.mp h1)
  rwa [hlog] at h2
