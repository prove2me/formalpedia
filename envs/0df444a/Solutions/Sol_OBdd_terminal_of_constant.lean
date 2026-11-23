-- Prove2me | solution 1 for OBdd.terminal_of_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:10:06.444839+00:00
-- url     : https://prove2.me/submissions/53efa733-0f08-4e76-bac8-1d32b43a0999

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_OBdd_high_reduced
import Theorems.Thm_OBdd_low_reduced
import Theorems.Thm_OBdd_evaluate_high_eq_evaluate_set_true
import Theorems.Thm_OBdd_evaluate_low_eq_evaluate_set_false
import Theorems.Thm_OBdd_not_reduced_of_sim_high_low
import Theorems.Thm_OBdd_Canonicity
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution (O : OBdd n m) :
    O.Reduced → O.evaluate = (fun _ ↦ b) → O.1.root = terminal b := by
  intro R h
  cases O_root_def : O.1.root
  case terminal b' =>
    rcases O with ⟨⟨heap, root⟩, o⟩
    subst O_root_def
    have he : (fun _ : Vector Bool n => b') = (fun _ => b) :=
      (congrArg DecisionTree.evaluate (OBdd.toTree_terminal (h := o))).symm.trans h
    exact congrArg Pointer.terminal (congrFun he (Vector.replicate n false))
  case node j =>
    exfalso
    refine not_reduced_of_sim_high_low O_root_def ?_ R
    have : (O.high O_root_def).evaluate = (O.low O_root_def).evaluate := by
      ext I
      trans b
      · simp [evaluate_high_eq_evaluate_set_true, h]
      · simp [evaluate_low_eq_evaluate_set_false, h]
    exact OBdd.Canonicity (high_reduced R) (low_reduced R) this
end OBdd
