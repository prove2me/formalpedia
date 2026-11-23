-- Prove2me | solution 1 for OBdd.eq_root_disjoint_reachable_low_or_high
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:04:59.083715+00:00
-- url     : https://prove2.me/submissions/1869c286-4787-48f4-8f38-928b5b11df98

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_OBdd_not_oedge_reachable
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} (h : O.1.root = node j) :
    Disjoint
      (· = O.1.root)
      (fun p ↦ (Reachable O.1.heap (O.low  h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p)) := by
  intro P h1 h2 p hp
  have this := h1 p hp
  have that := h2 p hp
  simp_all only
  cases that with
  | inl l =>
    rw [← h] at l
    apply OBdd.not_oedge_reachable oedge_of_low l
  | inr l =>
    rw [← h] at l
    apply OBdd.not_oedge_reachable oedge_of_high l
end OBdd
