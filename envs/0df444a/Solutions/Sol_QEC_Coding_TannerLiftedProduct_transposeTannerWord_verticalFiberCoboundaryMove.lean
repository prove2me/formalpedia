-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.transposeTannerWord_verticalFiberCoboundaryMove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:54:58.007475+00:00
-- url     : https://prove2.me/submissions/4b286128-cee5-481d-98ee-6bb42c985b00

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_transposeC0Word_verticalFiberCochain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_boundary2_transposeC0Word

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
    (edge : VerticalEdgeIndex W G) (u : Word F R) :
    transposeTannerWord inverseDirection
        (wordLinearMapTranspose (chainComplex label h h').boundary1
          (verticalFiberCochain edge u)) =
      (chainComplex targetLabel (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h)).boundary2
        (horizontalFiberChain
          (transposeVerticalEdge inverseDirection edge) u) := by
  rw [chainComplex, LiftedProduct.chainComplex_boundary1,
    chainComplex, LiftedProduct.chainComplex_boundary2,
    ← transposeC0Word_verticalFiberCochain inverseDirection edge u]
  exact (boundary2_transposeC0Word
    label targetLabel inverseDirection hInverse h h'
      (verticalFiberCochain edge u)).symm
end QEC.Coding.TannerLiftedProduct
