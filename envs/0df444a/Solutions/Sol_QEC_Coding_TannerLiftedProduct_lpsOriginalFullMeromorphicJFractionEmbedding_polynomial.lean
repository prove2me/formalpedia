-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFullMeromorphicJFractionEmbedding_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:38:46.442034+00:00
-- url     : https://prove2.me/submissions/577199bd-a286-4fa4-86b1-8a5c7aeabc71

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbedding_polynomial


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (P : Polynomial ℂ) :
    (lpsOriginalFullMeromorphicJFractionEmbedding N hN
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) P)).val.val =
      Filter.Germ.coeRingHom (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet)
        (lpsOriginalMeromorphicJFunctionCoefficient P) := by
  change (lpsOriginalHolomorphicFractionToMeromorphicGerm
    (lpsOriginalJFractionEmbedding (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) P))).val = _
  rw [lpsOriginalJFractionEmbedding_polynomial,
    lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic]
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall (fun z => lpsOriginalJHolomorphicEval_apply P
    (UpperHalfPlane.ofComplex z))
end QEC.Coding.TannerLiftedProduct
