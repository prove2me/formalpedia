-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:13:35.632113+00:00
-- url     : https://prove2.me/submissions/656e64b2-327f-4ee7-aac6-65f2a37cb0d2

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_chartNormalizedMeromorphicFunction_codiscrete
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledProjection_tendsto_codiscrete
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    lpsOriginalFilledMeromorphicRestriction N hN (lpsOriginalNormalizedFilledFunction N hN F)
      (lpsOriginalNormalizedFilledFunction_meromorphic N hN F hF) =
    lpsOriginalFilledMeromorphicRestriction N hN F hF := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  have he : F =ᶠ[Filter.codiscrete (LPSOriginalFilledCurve N)] lpsOriginalNormalizedFilledFunction N hN F :=
    chartNormalizedMeromorphicFunction_codiscrete F hF
  have hh : (fun z : ℂ => F (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z)))
      =ᶠ[Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet]
      (fun z : ℂ => lpsOriginalNormalizedFilledFunction N hN F
        (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z))) :=
    (lpsOriginalFilledProjection_tendsto_codiscrete N hN).eventually he
  exact hh.symm
end QEC.Coding.TannerLiftedProduct
