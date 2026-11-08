-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.semanticPresentation_boundedLocality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:19:54.484892+00:00
-- url     : https://prove2.me/submissions/06430b52-4f4a-4818-8eb2-e31ad748d8f9

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_boundary1RowSupport_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_boundary2RowSupport_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_variableSupport_le
import Theorems.Thm_QEC_Coding_FiniteFieldCSSPresentation_presentation_boundedLocality_of_boundaryIncidence_bounds


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe w
variable {F G W R R' : Type w}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_68799ef5cb_575
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F) :
    BoundedLocality
      (semanticPresentation label h g').localityProfile
      (2 * (Fintype.card W + Fintype.card R + Fintype.card R') *
        Fintype.card F) := by
  apply QEC.Coding.FiniteFieldCSSPresentation.presentation_boundedLocality_of_boundaryIncidence_bounds
  · intro c
    change ((LiftedProduct.boundaryIncidence (data label h g')).checkSupport c).card ≤
      2 * (Fintype.card W + Fintype.card R + Fintype.card R')
    cases c with
    | inl c0 =>
        rw [LiftedProduct.boundaryIncidence_checkSupport_inl]
        exact (card_boundary1RowSupport_le label h g' c0).trans (by omega)
    | inr c2 =>
        rw [LiftedProduct.boundaryIncidence_checkSupport_inr]
        exact (card_boundary2RowSupport_le label h g' c2).trans (by omega)
  · intro q
    change ((LiftedProduct.boundaryIncidence
      (data label h g')).variableSupport q).card ≤ _
    exact card_variableSupport_le label h g' q
end QEC.Coding.TannerLiftedProduct
