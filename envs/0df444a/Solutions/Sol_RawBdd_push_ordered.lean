-- Prove2me | solution 1 for RawBdd.push_ordered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:06:29.635174+00:00
-- url     : https://prove2.me/submissions/608cfce7-1e42-4c1b-832c-7203ccbf6d32

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_Bdd_ordered_of_ordered_heap_all_reachable_eq
import Theorems.Thm_RawBdd_RawPointer_cook_equiv
import Theorems.Thm_RawBdd_RawNode_cook_equiv
import Theorems.Thm_RawBdd_cook_low
import Theorems.Thm_RawBdd_cook_high
import Theorems.Thm_RawBdd_cook_inj
import Theorems.Thm_RawBdd_cook_aux
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const


section
set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace RawBdd
private lemma push_ordered_aux {v : Vector (RawNode n) m} {h0} {h2} :
    Pointer.Reachable (cook_heap (v.push N) h2) (RawPointer.cook p h3) q →
    ∀ j, q = .node j →
    ∃ hj : j.1 < m, Pointer.Reachable (cook_heap v h0) (p.cook h1) (.node ⟨j.1, hj⟩) := by
  intro h
  induction h with
  | refl =>
    intro i hi
    cases p with
    | inl val => contradiction
    | inr val =>
      simp [RawPointer.cook] at hi
      subst hi
      simp only
      use h1 rfl
      simp [RawPointer.cook]
      left
  | tail r e ih =>
    intro j hj
    rename_i b c
    cases e with
    | low heq =>
      rename_i jb
      have := h2 jb
      simp only [RawNode.Bounded] at this
      simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn] at heq
      subst hj
      have that : (v.push N)[jb].lo = .inr j.1 := by
        rw [show Pointer.node j = RawPointer.cook (.inr j.1) _ by rfl] at heq
        rw [← cook_low] at heq
        exact cook_inj heq
        apply RawPointer.bounded_of_le this.1
        omega
        simp [RawPointer.Bounded]
        intro i hi
        injection hi with heq
        rw [← heq]
        omega
      have : RawPointer.Bounded (↑jb) (v.push N)[jb].lo := this.1
      have := this that
      use lt_of_lt_of_le this (Nat.le_of_lt_succ jb.2)
      rcases (ih jb rfl) with ⟨r1, r2⟩
      trans .node ⟨jb.1, r1⟩
      · exact r2
      · simp_rw [Vector.getElem_push_lt r1] at heq
        right
        left
        left
        simp [cook_heap, RawNode.cook]
        simp [RawNode.cook] at heq
        exact cook_aux (h1 := RawPointer.bounded_of_le (h0 ⟨jb, r1⟩).1 (by omega))
          (h2 := RawPointer.bounded_of_le (h0 ⟨jb, r1⟩).1 (by omega)) heq
    | high heq =>
      rename_i jb
      have := h2 jb
      simp only [RawNode.Bounded] at this
      simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn] at heq
      subst hj
      have that : (v.push N)[jb].hi = .inr j.1 := by
        rw [show Pointer.node j = RawPointer.cook (.inr j.1) _ by rfl] at heq
        rw [← cook_high] at heq
        exact cook_inj heq
        apply RawPointer.bounded_of_le this.2
        omega
        simp [RawPointer.Bounded]
        intro i hi
        injection hi with heq
        rw [← heq]
        omega
      have : RawPointer.Bounded (↑jb) (v.push N)[jb].hi := this.2
      have := this that
      use lt_of_lt_of_le this (Nat.le_of_lt_succ jb.2)
      rcases (ih jb rfl) with ⟨r1, r2⟩
      trans .node ⟨jb.1, r1⟩
      · exact r2
      · simp_rw [Vector.getElem_push_lt r1] at heq
        right
        left
        right
        simp [cook_heap, RawNode.cook]
        simp [RawNode.cook] at heq
        exact cook_aux (h1 := RawPointer.bounded_of_le (h0 ⟨jb, r1⟩).2 (by omega))
          (h2 := RawPointer.bounded_of_le (h0 ⟨jb, r1⟩).2 (by omega)) heq
end RawBdd
end

set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
open RawBdd
namespace RawBdd
theorem _root_.solution : Bdd.Ordered ⟨cook_heap v h0, RawPointer.cook p h1⟩ → Bdd.Ordered ⟨cook_heap (v.push N) h2, RawPointer.cook p h3⟩ := by
  intro h
  apply Bdd.ordered_of_ordered_heap_all_reachable_eq ⟨⟨cook_heap v h0, RawPointer.cook p h1⟩, h⟩
  · intro j hj
    rcases (push_ordered_aux hj (h2 := h2) (h1 := h1) (h0 := h0) j rfl) with ⟨r1, r2⟩
    use r1
    simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_push_lt r1,
      RawNode.cook_equiv]
  · intro j hj
    simp_all only
    simp [RawPointer.cook] at hj
    split at hj
    next heq => contradiction
    next heq =>
      simp only [Pointer.node.injEq] at hj
      subst hj
      use h1 rfl
      simp [RawPointer.cook]
end RawBdd
