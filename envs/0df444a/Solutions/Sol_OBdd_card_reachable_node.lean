-- Prove2me | solution 1 for OBdd.card_reachable_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:10:32.356808+00:00
-- url     : https://prove2.me/submissions/f54c14ad-bed0-403d-8e97-32f6bdbbabb1

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_P2M_OBdd_card_reachable_node__da57529a8d4b
import Theorems.Thm_OBdd_eq_root_disjoint_reachable_low_or_high
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} (h : O.1.root = node j) :
  Fintype.card { q // Reachable O.1.heap O.1.root q } =
  1 + Fintype.card { q // Reachable (O.low h).1.heap (O.low h).1.root q ∨ Reachable (O.high h).1.heap (O.high h).1.root q } := by
  rw [card_reachable_node' h]
  rw [@Fintype.card_subtype_or_disjoint _ _ _ (eq_root_disjoint_reachable_low_or_high h) ..]
  · simp only [Fintype.card_unique, low_heap_eq_heap, add_right_inj]
    apply @Fintype.card_congr' ..
    · apply instFintypeEitherRelevantPointer (O.low h) (O.high h); simp
    · simp
  · exact Fintype.subtypeEq O.1.root
end OBdd
