-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.localVertexCosetLeaderMatrix_isDeltaMinimal_of_fiberLocallyMinimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:54:54.759975+00:00
-- url     : https://prove2.me/submissions/134b3f52-783f-4c38-9f12-e12bf4603cfc

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceMatrix_eq_localVertexCosetLeaderMatrix_of_mem_agreement
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceColumn_weight_le_add_codeword_of_fiberLocallyMinimal
import Theorems.Thm_QEC_Coding_ProductExpansion_IsCosetLeader_weight_le_add_codeword
import Theorems.Thm_QEC_Coding_ProductExpansion_fullRowRankCosetLeaderMatrix_isCosetLeader
import Theorems.Thm_QEC_Coding_ProductExpansion_isDeltaMinimal_of_rowLeaders_and_faceColumnMinimal


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
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (v : VertexIndex G) (m : Nat) (beta : ℝ)
    (hJ₃ : Fintype.card W - 2 * m ≤
      (localAgreementDirections label h hRank g' c v).card)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    ProductExpansion.IsDeltaMinimal h
      (ProductExpansion.generatorImageParityCheck g')
      (beta * Fintype.card W)
      (localVertexCosetLeaderMatrix h hRank g' c v) := by
  apply ProductExpansion.isDeltaMinimal_of_rowLeaders_and_faceColumnMinimal
    h (ProductExpansion.generatorImageParityCheck g')
    (localFaceMatrix label c v)
    (localVertexCosetLeaderMatrix h hRank g' c v)
    (localAgreementDirections label h hRank g' c v)
    m beta hJ₃
  · intro i hi j
    exact localFaceMatrix_eq_localVertexCosetLeaderMatrix_of_mem_agreement
      label h hRank g' c v i hi j
  · intro i codeword hcodeword
    exact (ProductExpansion.fullRowRankCosetLeaderMatrix_isCosetLeader
      h hRank (verticalVertexSyndrome g' c v) i).weight_le_add_codeword
        codeword hcodeword
  · intro j codeword hcodeword
    exact_mod_cast
      faceColumn_weight_le_add_codeword_of_fiberLocallyMinimal
        label h g' c hcLocal v j codeword hcodeword
  · exact hBudget
end QEC.Coding.TannerLiftedProduct
