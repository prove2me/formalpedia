-- Prove2me | solution 1 for P2M_OBdd_evaluate_node___75814e9183f4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:55:19.901549+00:00
-- url     : https://prove2.me/submissions/9c483586-843f-4438-9fe1-df67c0ca5b4f

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
theorem _root_.solution {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) :
    O.evaluate = fun I ↦ if I[O.1.heap[j].var] then (O.high h).evaluate I else (O.low h).evaluate I := by
  simp only [evaluate, Function.comp_apply]
  rw [toTree_node h]
  simp [DecisionTree.evaluate]
end OBdd
