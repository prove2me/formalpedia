-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.d_mul_card_nonactiveLabelledVertices_le_four_mul_faceSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:16:50.089023+00:00
-- url     : https://prove2.me/submissions/2edeff4f-fb9d-4b6a-a0ee-070539e66b8b

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_activeFaceIncidences_le_four_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_selectedFaceDirectionIncidences_le_activeFaceIncidences
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_d_mul_card_nonactiveLabelledVertices_le_selectedIncidences

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d m : Nat)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x) :
    d * (nonactiveLabelledVertices label c m).card ≤
      4 * (faceSupport c).card := by
  exact (d_mul_card_nonactiveLabelledVertices_le_selectedIncidences
    label h g' c hcCycle d m hDistance).trans
      ((card_selectedFaceDirectionIncidences_le_activeFaceIncidences
        label c m).trans
        (card_activeFaceIncidences_le_four_mul
          label c (labelledVertices label c m)))
end QEC.Coding.TannerLiftedProduct
