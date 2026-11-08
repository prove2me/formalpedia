-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.localStar_restrictedWeight_ge_on
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:07:40.642135+00:00
-- url     : https://prove2.me/submissions/aa4e74fa-2092-40a0-973c-7436d27a08db

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_IsCosetLeader_weight_le_add_codeword
import Theorems.Thm_QEC_Coding_ProductExpansion_fullRowRankCosetLeaderMatrix_isCosetLeader
import Theorems.Thm_QEC_Coding_ProductExpansion_isDeltaMinimal_of_rowLeaders_and_faceColumnMinimal
import Theorems.Thm_QEC_Coding_ProductExpansion_localStar_restrictedWeight_ge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceColumn_weight_le_add_codeword_of_fiberLocallyMinimal
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceMatrix_eq_localVertexCosetLeaderMatrix_of_mem_agreement
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceMatrix_row_heavy_of_mem_heavyDifference
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localVertexCosetLeaderMatrix_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localVertexCosetLeaderMatrix_productKernel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalInactiveDirections_eq_heavy_union_agreement


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
    (gInjective : Function.Injective
      (fun u : Word F R' => g'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (v : VertexIndex G) (hv : localVertexMatrix c v ≠ 0)
    (A B : Finset W)
    (hBInactive : B ⊆ verticalInactiveDirections label c v)
    (d m s : Nat) (beta : ℝ)
    (hExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hHorizontalLarge : Fintype.card W - m < A.card)
    (hVerticalLarge : Fintype.card W - m < B.card)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    s ≤ ProductExpansion.restrictedWeight (localFaceMatrix label c v) B A := by
  let J₂ := localHeavyDifferenceDirections label h hRank g' c v ∩ B
  let J₃ := localAgreementDirections label h hRank g' c v ∩ B
  apply ProductExpansion.localStar_restrictedWeight_ge
    h (ProductExpansion.generatorImageParityCheck g')
    (localFaceMatrix label c v)
    (localVertexCosetLeaderMatrix h hRank g' c v)
    A B J₂ J₃ d m s beta hExpand
  · exact localVertexCosetLeaderMatrix_productKernel h hRank g' c v
  · exact localVertexCosetLeaderMatrix_ne_zero
      h hRank g' gInjective c v hv
  · intro hJ₃
    apply ProductExpansion.isDeltaMinimal_of_rowLeaders_and_faceColumnMinimal
      h (ProductExpansion.generatorImageParityCheck g')
      (localFaceMatrix label c v)
      (localVertexCosetLeaderMatrix h hRank g' c v)
      J₃ m beta hJ₃
    · intro i hi j
      exact localFaceMatrix_eq_localVertexCosetLeaderMatrix_of_mem_agreement
        label h hRank g' c v i (Finset.mem_inter.mp hi).1 j
    · intro i codeword hcodeword
      exact (ProductExpansion.fullRowRankCosetLeaderMatrix_isCosetLeader
        h hRank (verticalVertexSyndrome g' c v) i).weight_le_add_codeword
          codeword hcodeword
    · intro j codeword hcodeword
      exact_mod_cast
        faceColumn_weight_le_add_codeword_of_fiberLocallyMinimal
          label h g' c hcLocal v j codeword hcodeword
    · exact hBudget
  · exact hHorizontalLarge
  · exact hVerticalLarge
  · intro b hb
    have hbInactive := hBInactive hb
    rw [verticalInactiveDirections_eq_heavy_union_agreement
      label h hRank g' c v] at hbInactive
    rcases Finset.mem_union.mp hbInactive with hbHeavy | hbAgree
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hbHeavy, hb⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hbAgree, hb⟩)
  · exact Finset.inter_subset_right
  · exact Finset.inter_subset_right
  · intro b hb
    exact localFaceMatrix_row_heavy_of_mem_heavyDifference
      label h hRank g' c hcCycle d hDistance v b
        (Finset.mem_inter.mp hb).1
  · exact hDistanceScale
  · exact hRectangleScale
  · intro b hb a _ha
    exact localFaceMatrix_eq_localVertexCosetLeaderMatrix_of_mem_agreement
      label h hRank g' c v b (Finset.mem_inter.mp hb).1 a
end QEC.Coding.TannerLiftedProduct
