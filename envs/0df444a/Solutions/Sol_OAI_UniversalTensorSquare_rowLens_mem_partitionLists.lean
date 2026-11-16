-- Prove2me | solution 1 for OAI.UniversalTensorSquare.rowLens_mem_partitionLists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:32:26.625797+00:00
-- url     : https://prove2.me/submissions/fdc12df6-0b01-408a-9f71-be604e9d3a0a

import Mathlib
import Definitions.Def_OAIQ259US001

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_FiniteDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Diagrams. -/

section

namespace UniversalTensorSquare

lemma mem_partitionLists (k : ℕ) (rs : List ℕ) (n b : ℕ)
    (hsum : rs.sum = n) (hlen : rs.length ≤ k)
    (hpos : ∀ a ∈ rs, 0 < a) (hbound : ∀ a ∈ rs, a ≤ b)
    (hsort : rs.SortedGE) : rs ∈ partitionLists k n b := by
  induction k generalizing rs n b with
  | zero =>
    have hr : rs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst rs
    simp only [List.sum_nil] at hsum
    subst n
    simp [partitionLists]
  | succ k ih =>
    cases rs with
    | nil =>
      simp only [List.sum_nil] at hsum
      subst n
      simp [partitionLists]
    | cons a rs =>
      have ha : 0 < a := hpos a (by simp)
      have han : a ≤ n := by simp only [List.sum_cons] at hsum; omega
      have hab : a ≤ b := hbound a (by simp)
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨a, Finset.mem_Icc.mpr ⟨ha, le_min han hab⟩, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨rs, ih rs (n-a) a ?_ ?_ ?_ ?_ ?_, rfl⟩
      · simp only [List.sum_cons] at hsum
        omega
      · simpa only [List.length_cons, Nat.succ_le_succ_iff] using hlen
      · intro x hx
        exact hpos x (by simp [hx])
      · intro x hx
        exact (List.pairwise_cons.mp hsort.pairwise).1 x hx
      · exact (List.pairwise_cons.mp hsort.pairwise).2.sortedGE

lemma rowLens_mem_partitionLists_oai (μ : YoungDiagram) :
    μ.rowLens ∈ partitionLists μ.card μ.card μ.card := by
  apply mem_partitionLists
  · exact (Saxl.card_eq_sum_rowLens μ).symm
  · rw [Saxl.card_eq_sum_rowLens]
    exact List.length_le_sum_of_one_le _ fun a ha => μ.pos_of_mem_rowLens a ha
  · exact fun a ha => μ.pos_of_mem_rowLens a ha
  · intro a ha
    rw [Saxl.card_eq_sum_rowLens]
    exact List.single_le_sum (fun x _ => Nat.zero_le x) a ha
  · exact μ.rowLens_sorted

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.rowLens_mem_partitionLists_oai := @OAI.UniversalTensorSquare.rowLens_mem_partitionLists_oai
