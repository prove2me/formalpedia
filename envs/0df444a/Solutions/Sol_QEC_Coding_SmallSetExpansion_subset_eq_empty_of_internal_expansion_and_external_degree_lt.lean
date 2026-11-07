-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.subset_eq_empty_of_internal_expansion_and_external_degree_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:43:00.202294+00:00
-- url     : https://prove2.me/submissions/72038ad1-635b-41f8-b354-b6273d4b1fc6

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_degree_mul_card_le_crossCount

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    [DecidableEq V]
    (M : WeightedGraph V) (radius : Nat) (lambda : ℝ)
    (A S : Finset V) (d m : Nat)
    (hExpand : IsSmallSetEdgeExpanding M radius lambda)
    (hSA : S ⊆ A) (hARadius : A.card ≤ radius)
    (hDegree : HasForwardDegreeAtLeast M S A d)
    (hExternal : ∀ v ∈ S,
      (∑ u ∈ A \ S, M v u) < 2 * m)
    (hThreshold : (2 * m : ℝ) + lambda ≤ d) :
    S = ∅ := by
  by_contra hS
  have hSNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  have hSRadius : S.card ≤ radius :=
    (Finset.card_le_card hSA).trans hARadius
  have hInternal := hExpand S S hSRadius hSRadius
  have hRoot : Real.sqrt ((S.card : ℝ) * S.card) = S.card := by
    rw [show (S.card : ℝ) * S.card = (S.card : ℝ) ^ 2 by ring]
    exact Real.sqrt_sq (Nat.cast_nonneg S.card)
  rw [hRoot] at hInternal
  have hExternalSum :
      crossCount M S (A \ S) < 2 * m * S.card := by
    unfold crossCount
    calc
      (∑ v ∈ S, ∑ u ∈ A \ S, M v u) <
          ∑ _v ∈ S, 2 * m :=
        Finset.sum_lt_sum_of_nonempty hSNonempty hExternal
      _ = 2 * m * S.card := by simp [Nat.mul_comm]
  have hASplit : A = S ∪ (A \ S) := by
    ext u
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hu
      by_cases huS : u ∈ S
      · exact Or.inl huS
      · exact Or.inr ⟨hu, huS⟩
    · rintro (huS | ⟨huA, _huS⟩)
      · exact hSA huS
      · exact huA
  have hDisjoint : Disjoint S (A \ S) := by
    exact Finset.disjoint_left.mpr fun u huS huDiff =>
      (Finset.mem_sdiff.mp huDiff).2 huS
  have hCrossSplit :
      crossCount M S A =
        crossCount M S S + crossCount M S (A \ S) := by
    have hInner : ∀ v,
        (∑ u ∈ A, M v u) =
          (∑ u ∈ S, M v u) + ∑ u ∈ A \ S, M v u := by
      intro v
      calc
        (∑ u ∈ A, M v u) = ∑ u ∈ S ∪ (A \ S), M v u := by
          exact Finset.sum_congr hASplit fun _u _hu => rfl
        _ = (∑ u ∈ S, M v u) + ∑ u ∈ A \ S, M v u :=
          Finset.sum_union hDisjoint
    unfold crossCount
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    exact hInner v
  have hDegreeSum := degree_mul_card_le_crossCount M S A d hDegree
  have hDegreeReal :
      (d : ℝ) * S.card ≤ (crossCount M S A : ℝ) := by
    exact_mod_cast hDegreeSum
  have hExternalReal :
      (crossCount M S (A \ S) : ℝ) <
        (2 * m : ℝ) * S.card := by
    exact_mod_cast hExternalSum
  rw [hCrossSplit, Nat.cast_add] at hDegreeReal
  have hSCardPos : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hSNonempty
  nlinarith
end QEC.Coding.SmallSetExpansion
