-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.transposeTannerWord_mem_horizontalFiberBoundaryMoves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:31:14.285475+00:00
-- url     : https://prove2.me/submissions/f66f07ef-8775-422a-b61c-f96a39a43039

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_transposeTannerWord_verticalFiberCoboundaryMove

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
    (m : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hm : m ∈ verticalFiberCoboundaryMoves label h h') :
    transposeTannerWord inverseDirection m ∈
      horizontalFiberBoundaryMoves targetLabel
        (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h) := by
  classical
  obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hm
  apply Finset.mem_image.mpr
  refine ⟨(transposeVerticalEdge inverseDirection p.1, p.2),
    Finset.mem_univ _, ?_⟩
  exact (transposeTannerWord_verticalFiberCoboundaryMove
    label targetLabel inverseDirection hInverse h h' p.1 p.2).symm
end QEC.Coding.TannerLiftedProduct
