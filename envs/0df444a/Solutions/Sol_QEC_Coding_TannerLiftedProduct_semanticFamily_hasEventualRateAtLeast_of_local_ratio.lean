-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.semanticFamily_hasEventualRateAtLeast_of_local_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:22:54.609912+00:00
-- url     : https://prove2.me/submissions/3113c5ba-5bd4-4996-a04e-2607b9d3cdaf

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerPairExistence
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerFamily
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rate_le_semanticPresentation_encodedQudits_of_local_ratio


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {A F W R R' : Type u} {G : A → Type u}
variable [Field F] [Fintype F]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
variable [∀ a, Group (G a)] [∀ a, Fintype (G a)]
variable [∀ a, DecidableEq (G a)]
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4063ed27f1_34
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4063ed27f1_35
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : ∀ a, W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W)
    (hGroupCofinal : ∀ N : Nat, ∃ a : A, N ≤ Fintype.card (G a))
    (rate : ℝ)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    QEC.QLDPC.HasEventualRateAtLeast
      (semanticFamily label h h' hW hGroupCofinal) rate := by
  refine ⟨0, ?_⟩
  intro a _ha
  exact rate_le_semanticPresentation_encodedQudits_of_local_ratio
    (label a) h h' rate hRatio
end QEC.Coding.TannerLiftedProduct
