-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspCoordinate_preferred_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:10:31.58721+00:00
-- url     : https://prove2.me/submissions/b31b7f8d-bc24-4229-897b-dd8c43807c4a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_eq_of_orbit_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoordinate_qParam_add
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspChange_translation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspRepresentative_orbit
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspRepresentative_range
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_cast
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspChart_cusp
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSignedTranslation_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    letI := lpsOriginalFilledTopology N
    let c := lpsOriginalCuspOrbit N ρ
    ∃ α : ℂ, α ≠ 0 ∧ ‖α‖ = 1 ∧ ∀ y : LPSOriginalFilledCurve N,
      y ∈ (lpsOriginalFilledCuspPartialEquiv N ρ).source →
      y ∈ (lpsOriginalFilledCuspChart N c).source ∧
      lpsOriginalFilledCuspChart N c y =
        α * lpsOriginalFilledCuspPartialEquiv N ρ y := by
  let := lpsOriginalFilledTopology N
  let c := lpsOriginalCuspOrbit N ρ
  let r := lpsOriginalCuspRepresentative N c
  let w := (lpsOriginalCuspGroup N ρ).strictWidthInfty
  obtain ⟨g,hg,u,hu⟩ := lpsOriginalCuspChange_translation N r ρ
    (lpsOriginalCuspRepresentative_orbit N c)
  let d := (Matrix.SpecialLinearGroup.mapGL ℝ r)⁻¹ * g *
    Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let α := Function.Periodic.qParam w (u : ℂ)
  have hw : (lpsOriginalCuspGroup N r).strictWidthInfty = w := by
    change (lpsOriginalCuspGroup N r).strictWidthInfty =
      (lpsOriginalCuspGroup N ρ).strictWidthInfty
    rw [lpsOriginalCuspWidthNat_cast, lpsOriginalCuspWidthNat_cast]
    exact congrArg (fun n : ℕ => (n : ℝ))
      (lpsOriginalCuspWidthNat_eq_of_orbit_eq N r ρ
        (lpsOriginalCuspRepresentative_orbit N c))
  refine ⟨α,Function.Periodic.qParam_ne_zero _,?_,?_⟩
  · simp [α,Function.Periodic.norm_qParam]
  · intro y hy
    have hs : y ∈ (lpsOriginalFilledCuspChart N c).source := by
      change y ∈ (lpsOriginalFilledCuspPartialEquiv N r).source
      cases y with
      | inl z =>
        change z ∈ Set.range (lpsOriginalCuspProjection N r)
        change z ∈ Set.range (lpsOriginalCuspProjection N ρ) at hy
        rw [lpsOriginalCuspRepresentative_range]
        exact hy
      | inr b =>
        change b = lpsOriginalCuspOrbit N r
        change b = c at hy
        rw [lpsOriginalCuspRepresentative_orbit]
        exact hy
    refine ⟨hs,?_⟩
    cases y with
    | inl z =>
      change z ∈ Set.range (lpsOriginalCuspProjection N ρ) at hy
      obtain ⟨σ,rfl⟩ := hy
      have hi : 1 < (d • σ.val).im := by
        rw [lpsSignedTranslation_im d u hu]
        exact σ.property
      let τ : {τ : ℍ // 1 < τ.im} := ⟨d • σ.val,hi⟩
      have hp : lpsOriginalCuspProjection N r τ =
          lpsOriginalCuspProjection N ρ σ := by
        apply Quotient.eq.mpr
        rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
        refine ⟨⟨g,hg⟩,?_⟩
        change g • (Matrix.SpecialLinearGroup.mapGL ℝ ρ • σ.val) =
          Matrix.SpecialLinearGroup.mapGL ℝ r • (d • σ.val)
        simp only [d,mul_smul,smul_inv_smul]
      have ht : (τ.val : ℂ) = (σ.val : ℂ)+(u : ℂ) := by
        change ((d • σ.val : ℍ) : ℂ) = _
        dsimp only [d]
        rcases hu with hplus | hminus
        · rw [hplus,lpsUpperRight_smul_coe]
        · rw [hminus,UpperHalfPlane.neg_smul,lpsUpperRight_smul_coe]
      change lpsOriginalFilledCuspPartialEquiv N r
        (Sum.inl (lpsOriginalCuspProjection N ρ σ)) =
          α * lpsOriginalFilledCuspPartialEquiv N ρ
            (Sum.inl (lpsOriginalCuspProjection N ρ σ))
      rw [←hp,lpsOriginalFilledCuspPartialEquiv_projection,ht,hw,
        lpsOriginalCuspCoordinate_qParam_add]
      rw [hp,lpsOriginalFilledCuspPartialEquiv_projection]
    | inr b =>
      change b = c at hy
      rw [hy,lpsOriginalFilledCuspChart_cusp]
      change 0 = α * 0
      exact (mul_zero α).symm
end QEC.Coding.TannerLiftedProduct
