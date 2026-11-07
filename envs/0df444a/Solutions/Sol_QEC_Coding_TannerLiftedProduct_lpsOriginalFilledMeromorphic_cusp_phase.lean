-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_cusp_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:34:07.398748+00:00
-- url     : https://prove2.me/submissions/521ab421-e304-4d37-8cc7-d481d442221d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicCusp_qParam_add
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
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (F : LPSOriginalFilledCurve N → ℂ) :
    letI := lpsOriginalFilledTopology N
    let c := lpsOriginalCuspOrbit N ρ
    let r := lpsOriginalCuspRepresentative N c
    let w := (lpsOriginalCuspGroup N r).strictWidthInfty
    ∃ α : ℂ, α ≠ 0 ∧ ∀ σ : {τ : ℍ // 1 < τ.im},
      F (Sum.inl (lpsOriginalCuspProjection N ρ σ)) =
        F ((lpsOriginalFilledCuspChart N c).symm
          (α * Function.Periodic.qParam w (σ.val : ℂ))) := by
  let := lpsOriginalFilledTopology N
  let c := lpsOriginalCuspOrbit N ρ
  let r := lpsOriginalCuspRepresentative N c
  let w := (lpsOriginalCuspGroup N r).strictWidthInfty
  obtain ⟨g,hg,x,hx⟩ := lpsOriginalCuspChange_translation N r ρ
    (lpsOriginalCuspRepresentative_orbit N c)
  let d := (Matrix.SpecialLinearGroup.mapGL ℝ r)⁻¹ * g *
    Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let α := Function.Periodic.qParam w (x : ℂ)
  refine ⟨α,Function.Periodic.qParam_ne_zero _,?_⟩
  intro σ
  have hi : 1 < (d • σ.val).im := by
    rw [lpsSignedTranslation_im d x hx]
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
  have ht : (τ.val : ℂ) = (σ.val : ℂ)+(x : ℂ) := by
    change ((d • σ.val : ℍ) : ℂ) = _
    dsimp only [d]
    rcases hx with hplus | hminus
    · rw [hplus,lpsUpperRight_smul_coe]
    · rw [hminus,UpperHalfPlane.neg_smul,lpsUpperRight_smul_coe]
  let e := lpsOriginalFilledCuspChart N c
  have hs : Sum.inl (lpsOriginalCuspProjection N r τ) ∈ e.source := ⟨τ,rfl⟩
  have hq : e (Sum.inl (lpsOriginalCuspProjection N r τ)) =
      α * Function.Periodic.qParam w (σ.val : ℂ) := by
    change lpsOriginalFilledCuspPartialEquiv N r
      (Sum.inl (lpsOriginalCuspProjection N r τ)) = _
    rw [lpsOriginalFilledCuspPartialEquiv_projection,ht,
      lpsOriginalMeromorphicCusp_qParam_add]
  rw [←hp,← e.left_inv hs,hq]
end QEC.Coding.TannerLiftedProduct
