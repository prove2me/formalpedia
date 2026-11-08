-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.algebraicCSSMinimumDistance_le_semanticPresentation_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:45:23.628794+00:00
-- url     : https://prove2.me/submissions/407cd8df-61e3-4539-afa2-4e008f4590aa

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_algebraicCSSMinimumDistance_le_semanticQuditDistance
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_distance_eq_semanticQuditDistance


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_138d9bf296_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_138d9bf296_24
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (dCSS : Nat)
    (hMinimum : AlgebraicCSSMinimumDistance
      (chainComplex label h h').firstCoboundaryCheckCode
      (chainComplex label h h').middleBoundaryCode dCSS) :
    dCSS ≤ (semanticPresentation label h h').distance := by
  classical
  rw [(semanticPresentation label h h').distance_eq_semanticQuditDistance]
  exact QEC.Coding.FiniteFieldPauli.algebraicCSSMinimumDistance_le_semanticQuditDistance
    (chainComplex label h h').firstCoboundaryCheckCode
    (chainComplex label h h').middleBoundaryCode
    (chainComplex label h h').firstCoboundaryCheckCode_le_middleBoundaryCode_dual
    dCSS hMinimum
end QEC.Coding.TannerLiftedProduct
