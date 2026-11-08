-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.faceColumn_weight_le_add_codeword_of_fiberLocallyMinimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:52:20.807289+00:00
-- url     : https://prove2.me/submissions/685b79c2-81cc-4974-a4ae-9ec1a2b5d298

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceColumn_weight_le_add_generator_of_fiberLocallyMinimal
import Theorems.Thm_QEC_Coding_ProductExpansion_mem_generatorImage_iff
import Theorems.Thm_QEC_Coding_ProductExpansion_parityCheckCode_generatorImageParityCheck_carrier


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
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (v : VertexIndex G) (a : W) (delta : Word F W)
    (hdelta : delta ∈
      (ProductExpansion.parityCheckCode
        (ProductExpansion.generatorImageParityCheck g')).carrier) :
    HammingWeight
        (ProductExpansion.column (localFaceMatrix label c v) a) ≤
      HammingWeight
        (ProductExpansion.column (localFaceMatrix label c v) a + delta) + 2 := by
  rw [ProductExpansion.parityCheckCode_generatorImageParityCheck_carrier] at hdelta
  rw [ProductExpansion.mem_generatorImage_iff] at hdelta
  obtain ⟨u, hu⟩ := hdelta
  rw [← hu]
  exact faceColumn_weight_le_add_generator_of_fiberLocallyMinimal
    label h g' c hcLocal v a u
end QEC.Coding.TannerLiftedProduct
