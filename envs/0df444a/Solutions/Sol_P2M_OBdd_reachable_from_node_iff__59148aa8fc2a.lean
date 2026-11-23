-- Prove2me | solution 1 for P2M_OBdd_reachable_from_node_iff__59148aa8fc2a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:04:31.437466+00:00
-- url     : https://prove2.me/submissions/d8765bcd-dc3f-4cea-9e30-23f435b8f6fe

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} (h : O.1.root = node j) :
    Reachable O.1.heap O.1.root p ↔ p = O.1.root ∨ (Reachable O.1.heap (O.low h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p) := by
  constructor
  · intro r
    cases (Relation.reflTransGen_swap.mp r) with
    | refl => left; rfl
    | tail t e =>
      rename_i q
      right
      rw [h] at e
      cases e with
      | low  l =>
        left
        trans q
        · simp only [low,Bdd.low, l]
          left
        · exact Relation.reflTransGen_swap.mp t
      | high l =>
        right
        trans q
        · simp only [high, Bdd.high, l]
          left
        · exact Relation.reflTransGen_swap.mp t
  · intro r
    cases r with
    | inl r =>
      rw [r]
      left
    | inr r =>
      cases r with
      | inl r =>
        apply Relation.reflTransGen_swap.mpr
        apply Relation.ReflTransGen.tail (Relation.reflTransGen_swap.mpr r)
        simp [Function.swap]
        exact edge_of_low  (h := h)
      | inr r =>
        apply Relation.reflTransGen_swap.mpr
        apply Relation.ReflTransGen.tail (Relation.reflTransGen_swap.mpr r)
        simp [Function.swap]
        exact edge_of_high (h := h)
end OBdd
