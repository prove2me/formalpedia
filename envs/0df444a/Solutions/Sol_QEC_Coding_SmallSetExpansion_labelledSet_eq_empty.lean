-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.labelledSet_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:43:01.48355+00:00
-- url     : https://prove2.me/submissions/253793a2-ae5e-4464-99c7-94e5bb9b3871

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_four_mul_card_le_of_degree_and_expansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    [DecidableEq V]
    (M₁ M₂ : WeightedGraph V)
    (radius₁ radius₂ degree₁ degree₂ : Nat)
    (lambda₁ lambda₂ : ℝ)
    (hLambda₁ : 0 < lambda₁) (hLambda₂ : 0 < lambda₂)
    (hExpand₁ : IsSmallSetEdgeExpanding M₁ radius₁ lambda₁)
    (hExpand₂ : IsSmallSetEdgeExpanding M₂ radius₂ lambda₂)
    (L L₁ L₂ : Finset V)
    (hCover : L ⊆ L₁ ∪ L₂)
    (hL₁ : L₁ ⊆ L) (hL₂ : L₂ ⊆ L)
    (hLRadius₁ : L.card ≤ radius₁)
    (hLRadius₂ : L.card ≤ radius₂)
    (hDegree₁ : HasForwardDegreeAtLeast M₁ L₁ L degree₁)
    (hDegree₂ : HasForwardDegreeAtLeast M₂ L₂ L degree₂)
    (hThreshold₁ : 2 * lambda₁ ≤ degree₁)
    (hThreshold₂ : 2 * lambda₂ ≤ degree₂) :
    L = ∅ := by
  have hL₁Radius : L₁.card ≤ radius₁ :=
    (Finset.card_le_card hL₁).trans hLRadius₁
  have hL₂Radius : L₂.card ≤ radius₂ :=
    (Finset.card_le_card hL₂).trans hLRadius₂
  have hQuarter₁ : 4 * L₁.card ≤ L.card :=
    four_mul_card_le_of_degree_and_expansion M₁ radius₁ degree₁ lambda₁
      hLambda₁ hExpand₁ L₁ L hL₁Radius hLRadius₁ hDegree₁ hThreshold₁
  have hQuarter₂ : 4 * L₂.card ≤ L.card :=
    four_mul_card_le_of_degree_and_expansion M₂ radius₂ degree₂ lambda₂
      hLambda₂ hExpand₂ L₂ L hL₂Radius hLRadius₂ hDegree₂ hThreshold₂
  have hCardCover : L.card ≤ L₁.card + L₂.card := by
    exact (Finset.card_le_card hCover).trans (Finset.card_union_le L₁ L₂)
  have : L.card = 0 := by omega
  exact Finset.card_eq_zero.mp this
end QEC.Coding.SmallSetExpansion
