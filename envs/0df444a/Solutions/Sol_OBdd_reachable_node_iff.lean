-- Prove2me | solution 1 for OBdd.reachable_node_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:10:21.045016+00:00
-- url     : https://prove2.me/submissions/6a9a915e-bb27-4008-ae3e-7c1f85f5793e

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic

set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} (h : O.1.root = node j) :
  Reachable O.1.heap O.1.root = fun q ↦
    (Reachable O.1.heap O.1.root q ∧ ¬ Reachable O.1.heap (O.low h).1.root q ∧ ¬ Reachable O.1.heap (O.high h).1.root q) ∨
    (Reachable O.1.heap (O.low  h).1.root q ∧ ¬ Reachable O.1.heap (O.high h).1.root q) ∨
    (Reachable O.1.heap (O.high h).1.root q ∧ ¬ Reachable O.1.heap (O.low  h).1.root q) ∨
    (Reachable O.1.heap (O.low  h).1.root q ∧   Reachable O.1.heap (O.high h).1.root q) := by
  ext p
  constructor
  · intro r
    cases instDecidableReachable (O.low h) p with
    | isFalse hf =>
      cases instDecidableReachable (O.high h) p with
      | isFalse hhf =>
        left
        exact ⟨r, hf, hhf⟩
      | isTrue hht =>
        right
        right
        left
        exact ⟨hht, hf⟩
    | isTrue ht =>
      cases instDecidableReachable (O.high h) p with
      | isFalse hhf =>
        right
        left
        exact ⟨ht, hhf⟩
      | isTrue hht =>
        right
        right
        right
        exact ⟨ht, hht⟩
  · intro r
    cases r with
    | inl r => exact r.1
    | inr r =>
      cases r with
      | inl r =>
        trans (O.low h).1.root
        · exact reachable_of_edge (edge_of_low (h := h) O.1)
        · exact r.1
      | inr r =>
        cases r with
        | inl r =>
          trans (O.high h).1.root
          · exact reachable_of_edge (edge_of_high (h := h) O.1)
          · exact r.1
        | inr r =>
          trans (O.high h).1.root
          · exact reachable_of_edge (edge_of_high (h := h) O.1)
          · exact r.2
end OBdd
