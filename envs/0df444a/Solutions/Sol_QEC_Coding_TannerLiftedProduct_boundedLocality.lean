-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.boundedLocality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:19:52.894698+00:00
-- url     : https://prove2.me/submissions/e2ce26f5-a818-43e1-9177-b654642ca4ee

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_boundary1RowSupport_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_boundary2RowSupport_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_variableSupport_le
import Theorems.Thm_QEC_Coding_LiftedProduct_boundaryIncidence_boundedLocality_of_bounds


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.LiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F) :
    QEC.Coding.BoundedLocality
      (LiftedProduct.boundaryIncidence (data label h g')).localityProfile
      (2 * (Fintype.card W + Fintype.card R + Fintype.card R')) := by
  apply LiftedProduct.boundaryIncidence_boundedLocality_of_bounds
  · intro c0
    exact (card_boundary1RowSupport_le label h g' c0).trans (by omega)
  · intro c2
    exact (card_boundary2RowSupport_le label h g' c2).trans (by omega)
  · exact card_variableSupport_le label h g'
end QEC.Coding.TannerLiftedProduct
