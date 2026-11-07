-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.localStar_restrictedWeight_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:44:59.975481+00:00
-- url     : https://prove2.me/submissions/b98e6be2-ebd9-4431-a32d-139fc178c2a3

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_restrictedWeight_ge_of_many_heavy_rows
import Theorems.Thm_QEC_Coding_ProductExpansion_restrictedWeight_ge_of_productExpanding_agreement

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F)
    (f t : Matrix W W F) (A B J₂ J₃ : Finset W)
    (d m s : Nat) (beta : ℝ)
    (hExpand : ProductExpanding h h' s (2 * m) beta)
    (hKernel : ProductKernel h h' t) (hNonzero : t ≠ 0)
    (hMinimal : Fintype.card W - 2 * m ≤ J₃.card →
      IsDeltaMinimal h h' (beta * Fintype.card W) t)
    (hA : Fintype.card W - m < A.card)
    (hB : Fintype.card W - m < B.card)
    (hCover : B ⊆ J₂ ∪ J₃)
    (hJ₂B : J₂ ⊆ B) (hJ₃B : J₃ ⊆ B)
    (hHeavy : ∀ i ∈ J₂, d ≤ 2 * HammingWeight (row f i))
    (hDistance : 4 * m ≤ d)
    (hScale : 4 * s ≤ m * d)
    (hAgree : ∀ i ∈ J₃, ∀ j ∈ A, f i j = t i j) :
    s ≤ restrictedWeight f B A := by
  by_cases hJ₃Large : Fintype.card W - 2 * m ≤ J₃.card
  · apply restrictedWeight_ge_of_productExpanding_agreement
      h h' f t A B J₃ s m beta hExpand hKernel hNonzero
        (hMinimal hJ₃Large)
    · omega
    · exact hJ₃Large
    · exact hJ₃B
    · exact hAgree
  · have hCardCover : B.card ≤ J₂.card + J₃.card :=
      (Finset.card_le_card hCover).trans (Finset.card_union_le J₂ J₃)
    have hCount : m < J₂.card := by omega
    apply restrictedWeight_ge_of_many_heavy_rows
      f A B J₂ d m s hJ₂B
    · omega
    · exact hCount
    · exact hHeavy
    · exact hDistance
    · exact hScale
end QEC.Coding.ProductExpansion
