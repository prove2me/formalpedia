-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.rate_le_semanticPresentation_encodedQudits_of_local_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:16:45.549616+00:00
-- url     : https://prove2.me/submissions/8cf16800-c776-496d-b2bd-abbdfa0dd771

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rate_le_finrank_middleHomology_of_local_ratio


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
    (rate : ℝ)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    rate * ((semanticPresentation label h h').blockLength : ℝ) ≤
      ((semanticPresentation label h h').encodedQudits : ℝ) := by
  change rate * Fintype.card
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) ≤
    (Module.finrank F (chainComplex label h h').middleHomology : ℝ)
  exact rate_le_finrank_middleHomology_of_local_ratio label h h' rate hRatio
end QEC.Coding.TannerLiftedProduct
