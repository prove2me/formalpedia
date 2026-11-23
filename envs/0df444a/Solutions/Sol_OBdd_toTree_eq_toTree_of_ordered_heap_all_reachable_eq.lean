-- Prove2me | solution 1 for OBdd.toTree_eq_toTree_of_ordered_heap_all_reachable_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:00:40.736332+00:00
-- url     : https://prove2.me/submissions/82ff9293-9c4b-4c09-9d01-8579b17dcd40

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_P2M_OBdd_toTree_terminal__6f80b985dd51
import Theorems.Thm_Pointer_equiv_symm
import Theorems.Thm_Node_equiv_symm
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution (O : OBdd n m) (U : OBdd n m') :
    (∀ j : Fin m', Reachable U.1.heap U.1.root (node j) → ∃ hj : j.1 < m, Node.equiv O.1.heap[j.1] U.1.heap[j]) →
    Pointer.equiv U.1.root O.1.root →
    O.toTree = U.toTree := by
  intro h1 h2
  cases U_root_def : U.1.root with
  | terminal b =>
    simp only [Pointer.equiv] at h2
    have := h2.1 b U_root_def
    simp_all [OBdd.toTree_terminal']
  | node j =>
    simp only [Pointer.equiv] at h2
    have := h2.2 j U_root_def
    rcases this with ⟨j', hj', hjj'⟩
    rw [OBdd.toTree_node U_root_def]
    rw [OBdd.toTree_node hj']
    have := h1 j (by simp [U_root_def]; left)
    rcases this with ⟨hj, hev, hel, heh⟩
    congr 1
    · simp_all; apply Fin.eq_of_val_eq; exact hev
    · apply solution
      · intro jj hrjj
        simp only [low_heap_eq_heap]
        apply h1
        apply Relation.reflTransGen_swap.mpr
        right
        exact Relation.reflTransGen_swap.mp hrjj
        exact oedge_of_low.2
      · simp_all [OBdd.low, Bdd.low]
        exact Pointer.equiv_symm hel
    · apply solution
      · intro jj hrjj
        simp only [high_heap_eq_heap]
        apply h1
        apply Relation.reflTransGen_swap.mpr
        right
        exact Relation.reflTransGen_swap.mp hrjj
        exact oedge_of_high.2
      · simp_all [OBdd.high, Bdd.high]
        exact Pointer.equiv_symm heh
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
end OBdd
