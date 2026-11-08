-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledNoInteriorPole_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:28:47.130102+00:00
-- url     : https://prove2.me/submissions/56ebc27a-027b-4c56-bedc-1a4833bb1cbd

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledFunction_restriction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledFunction_upstairs_holomorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledHolomorphic_integral


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hno : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ x : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
      0 ≤ meromorphicOrderAt (F ∘ (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N) (Sum.inl x))) :
    letI := ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).toAlgebra
    IsIntegral (Polynomial ℂ) (lpsOriginalFilledMeromorphicRestriction N hN F hF) := by
  have hi := lpsOriginalFilledHolomorphic_integral N hN
    (lpsOriginalNormalizedFilledFunction N hN F)
    (lpsOriginalNormalizedFilledFunction_meromorphic N hN F hF)
    (lpsOriginalNormalizedFilledFunction_upstairs_holomorphic N hN F hF hno)
  rwa [lpsOriginalNormalizedFilledFunction_restriction] at hi
end QEC.Coding.TannerLiftedProduct
