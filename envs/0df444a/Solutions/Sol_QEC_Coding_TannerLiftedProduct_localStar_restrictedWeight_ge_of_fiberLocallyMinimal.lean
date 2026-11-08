-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.localStar_restrictedWeight_ge_of_fiberLocallyMinimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:37:49.70822+00:00
-- url     : https://prove2.me/submissions/8fce5f35-e25f-430d-8607-0d750ab9dfa7

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localVertexCosetLeaderMatrix_productKernel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localVertexCosetLeaderMatrix_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalInactiveDirections_eq_heavy_union_agreement
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceMatrix_eq_localVertexCosetLeaderMatrix_of_mem_agreement
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localHeavyDifferenceDirections_subset_verticalInactiveDirections
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localAgreementDirections_subset_verticalInactiveDirections
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceMatrix_row_heavy_of_mem_heavyDifference
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localVertexCosetLeaderMatrix_isDeltaMinimal_of_fiberLocallyMinimal
import Theorems.Thm_QEC_Coding_ProductExpansion_localStar_restrictedWeight_ge


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
    (d m s : Nat) (beta : ℝ)
    (hExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hHorizontalLarge : Fintype.card W - m <
      (horizontalInactiveDirections label c v).card)
    (hVerticalLarge : Fintype.card W - m <
      (verticalInactiveDirections label c v).card)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    s ≤ ProductExpansion.restrictedWeight (localFaceMatrix label c v)
      (verticalInactiveDirections label c v)
      (horizontalInactiveDirections label c v) := by
  apply ProductExpansion.localStar_restrictedWeight_ge
    h (ProductExpansion.generatorImageParityCheck g')
    (localFaceMatrix label c v)
    (localVertexCosetLeaderMatrix h hRank g' c v)
    (horizontalInactiveDirections label c v)
    (verticalInactiveDirections label c v)
    (localHeavyDifferenceDirections label h hRank g' c v)
    (localAgreementDirections label h hRank g' c v)
    d m s beta hExpand
  · exact localVertexCosetLeaderMatrix_productKernel h hRank g' c v
  · exact localVertexCosetLeaderMatrix_ne_zero
      h hRank g' gInjective c v hv
  · intro hJ₃
    exact localVertexCosetLeaderMatrix_isDeltaMinimal_of_fiberLocallyMinimal
      label h hRank g' c hcLocal v m beta hJ₃ hBudget
  · exact hHorizontalLarge
  · exact hVerticalLarge
  · intro b hb
    rw [← verticalInactiveDirections_eq_heavy_union_agreement
      label h hRank g' c v]
    exact hb
  · exact localHeavyDifferenceDirections_subset_verticalInactiveDirections
      label h hRank g' c v
  · exact localAgreementDirections_subset_verticalInactiveDirections
      label h hRank g' c v
  · intro b hb
    exact localFaceMatrix_row_heavy_of_mem_heavyDifference
      label h hRank g' c hcCycle d hDistance v b hb
  · exact hDistanceScale
  · exact hRectangleScale
  · intro b hb a _ha
    exact localFaceMatrix_eq_localVertexCosetLeaderMatrix_of_mem_agreement
      label h hRank g' c v b hb a
end QEC.Coding.TannerLiftedProduct
