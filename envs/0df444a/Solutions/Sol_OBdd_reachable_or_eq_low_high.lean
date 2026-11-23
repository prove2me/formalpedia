-- Prove2me | solution 1 for OBdd.reachable_or_eq_low_high
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:00:12.332486+00:00
-- url     : https://prove2.me/submissions/8a861445-bdad-459e-be07-070dd06cc526

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_Pointer_Reachable_iff
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} :
    Reachable O.1.heap O.1.root p → (O.1.root = p ∨ (∃ j, ∃ (h : O.1.root = node j), (Reachable O.1.heap (O.low h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p))) := by
  intro hr
  cases Reachable_iff.mp hr with
  | inl => left; assumption
  | inr h =>
    right
    rcases h with ⟨j, O_root_def, hj⟩
    use j, O_root_def
    cases hj with
    | inl hl => left;  simpa [low, Bdd.low]
    | inr hh => right; simpa [high, Bdd.high]
end OBdd
