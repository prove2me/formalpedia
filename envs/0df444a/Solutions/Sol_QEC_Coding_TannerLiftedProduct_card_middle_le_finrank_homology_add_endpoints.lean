-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_middle_le_finrank_homology_add_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:18:09.063527+00:00
-- url     : https://prove2.me/submissions/0b6f26bb-8fc7-421a-9072-c693e74fb3b2

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_c0Index
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_c2Index
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_chainComplex_middle_card
import Theorems.Thm_QEC_Coding_LiftedProduct_card_qubitIndex_le_finrank_middleHomology_add_endpoints


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
    Fintype.card G *
        (Fintype.card W ^ 2 + 4 * Fintype.card R * Fintype.card R') ≤
      Module.finrank F (LiftedProduct.chainComplex (data label h g')).middleHomology +
        2 * Fintype.card R * Fintype.card W * Fintype.card G +
        2 * Fintype.card R' * Fintype.card W * Fintype.card G := by
  have hBound :=
    LiftedProduct.card_qubitIndex_le_finrank_middleHomology_add_endpoints
      (data label h g')
  rw [chainComplex_middle_card (G := G) (W := W) (R := R) (R' := R'),
    card_c0Index (G := G) (W := W) (R := R),
    card_c2Index (G := G) (W := W) (R' := R')] at hBound
  exact hBound
end QEC.Coding.TannerLiftedProduct
