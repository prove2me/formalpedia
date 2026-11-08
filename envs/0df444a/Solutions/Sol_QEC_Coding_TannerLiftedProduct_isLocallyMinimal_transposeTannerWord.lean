-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.isLocallyMinimal_transposeTannerWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:34:43.273944+00:00
-- url     : https://prove2.me/submissions/3e617a79-d8dd-43b6-9e71-20adae794418

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_blockWeight_transposeTannerWord
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_transposeTannerWord_add
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_verticalFiberCoboundaryMove_of_mem_horizontal

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
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hzLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (verticalFiberCoboundaryMoves label h h') z) :
    LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves targetLabel
        (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h))
      (transposeTannerWord inverseDirection z) := by
  intro m' hm'
  obtain ⟨m, hm, rfl⟩ :=
    exists_verticalFiberCoboundaryMove_of_mem_horizontal
      label targetLabel inverseDirection hInverse h h' m' hm'
  rw [← transposeTannerWord_add, blockWeight_transposeTannerWord,
    blockWeight_transposeTannerWord]
  exact hzLocal m hm
end QEC.Coding.TannerLiftedProduct
