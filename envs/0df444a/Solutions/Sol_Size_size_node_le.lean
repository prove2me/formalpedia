-- Prove2me | solution 1 for Size.size_node_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:09:57.20125+00:00
-- url     : https://prove2.me/submissions/55524f82-0b24-4066-ac27-6eb967e6a164

import Definitions.Def_Bdd_Collect
import Definitions.Def_Bdd_Size
import Theorems.Thm_Size_size_spec
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_OBdd_reachable_or_eq_low_high
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Size
namespace Size
theorem _root_.solution {O : OBdd n m} {h : O.1.root = .node j} :
    size O ≤ 1 + (size (O.low h)) + (size (O.high h)) := by
  repeat rw [size_spec]
  repeat rw [OBdd.size]
  rw [show 1 = Fintype.card {j' // j' = j} by simp]
  rw [add_assoc]
  rw [← Fintype.card_sum]
  rw [← Fintype.card_sum]
  refine Fintype.card_le_of_embedding ⟨?_, ?_⟩
  · exact
    fun ⟨j', hj'⟩ ↦ match decEq j' j with
      | isTrue ht => .inl ⟨j', ht⟩
      | isFalse hf => .inr (
        match Pointer.instDecidableReachable (O.low h) (.node j') with
        | isTrue htt => .inl ⟨j', htt⟩
        | isFalse hff => .inr ⟨j', by
          apply OBdd.reachable_or_eq_low_high at hj'
          cases hj' with
          | inl hh => simp_all
          | inr hh =>
            rcases hh with ⟨jj, hjj1, hjj2⟩
            have : Pointer.node j = .node jj := by rw [← h, hjj1]
            injection this with that
            subst that
            cases hjj2 with
            | inl hhh => simp_all
            | inr hhh => exact hhh
          ⟩
        )
  · intro x y hxy
    simp only [OBdd.low_heap_eq_heap, OBdd.high_heap_eq_heap] at hxy
    split at hxy
    next =>
      split at hxy <;> (refine Subtype.ext ?_; simp_all <;> exact (congrArg (fun z => z.val) hxy : _))
    next =>
      split at hxy <;>
      (next =>
        split at hxy
        next => simp_all
        next => split at hxy <;> (refine Subtype.ext ?_; simp_all <;> exact (congrArg (fun z => z.val) hxy : _)))
end Size
