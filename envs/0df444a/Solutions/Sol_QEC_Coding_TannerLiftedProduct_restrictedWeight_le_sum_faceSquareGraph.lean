-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.restrictedWeight_le_sum_faceSquareGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:54:05.920142+00:00
-- url     : https://prove2.me/submissions/ea234167-6e20-4b9b-8b32-bdbba63fb87a

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sum_faceSquareGraph_eq_card_filter
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_activeFaceDirectionPairs

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [Fintype G] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (A B : Finset W)
    (L : Finset (VertexIndex G))
    (hOpposite : ∀ a ∈ A, ∀ b ∈ B,
      localFaceMatrix label c v b a ≠ 0 →
        verticalNeighbor label (horizontalNeighbor label v a) b ∈ L) :
    ProductExpansion.restrictedWeight (localFaceMatrix label c v) B A ≤
      ∑ u ∈ L, faceSquareGraph label v u := by
  rw [← card_activeFaceDirectionPairs label c v A B,
    sum_faceSquareGraph_eq_card_filter]
  apply Finset.card_le_card
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpAB := Finset.mem_product.mp hpData.1
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ p,
    hOpposite p.1 hpAB.1 p.2 hpAB.2 hpData.2⟩
end QEC.Coding.TannerLiftedProduct
