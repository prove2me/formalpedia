-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.localVertexCosetLeaderMatrix_productKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:46:58.382751+00:00
-- url     : https://prove2.me/submissions/c9a40f11-b5d0-4621-b82d-9e9cb96d9f24

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_generatorImageParityCheck_mul_verticalVertexSyndrome_eq_zero
import Theorems.Thm_QEC_Coding_ProductExpansion_fullRowRankCosetLeaderMatrix_productKernel


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Group G] [Fintype G] [DecidableEq G]
    [DecidableEq R] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    ProductExpansion.ProductKernel h
      (ProductExpansion.generatorImageParityCheck h')
      (localVertexCosetLeaderMatrix h hRank h' c v) := by
  exact ProductExpansion.fullRowRankCosetLeaderMatrix_productKernel
    h (ProductExpansion.generatorImageParityCheck h') hRank
    (verticalVertexSyndrome h' c v)
    (generatorImageParityCheck_mul_verticalVertexSyndrome_eq_zero h' c v)
end QEC.Coding.TannerLiftedProduct
