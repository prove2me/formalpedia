-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledHolomorphic_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:01:06.449988+00:00
-- url     : https://prove2.me/submissions/3dafdae6-d03b-4041-9e4e-4cbbbf130655

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.Algebra.Polynomial.BigOperators
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledHolomorphic_exists_monic_annihilator
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_nested_annihilator_germ


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => F (Sum.inl ⟦τ⟧))) :
    letI := ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).toAlgebra
    IsIntegral (Polynomial ℂ) (lpsOriginalFilledMeromorphicRestriction N hN F hF) := by
  let := ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
    (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).toAlgebra
  obtain ⟨Φ,hmonic,hroot⟩ := lpsOriginalFilledHolomorphic_exists_monic_annihilator N hN F hF hhol
  refine ⟨Φ,hmonic,?_⟩
  change Φ.eval₂ ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
    (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ))))
      (lpsOriginalFilledMeromorphicRestriction N hN F hF) = 0
  exact lpsOriginalFilledMeromorphic_nested_annihilator_germ N hN F hF Φ hroot
end QEC.Coding.TannerLiftedProduct
