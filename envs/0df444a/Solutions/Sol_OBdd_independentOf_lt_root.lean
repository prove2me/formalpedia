-- Prove2me | solution 1 for OBdd.independentOf_lt_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:56:21.187945+00:00
-- url     : https://prove2.me/submissions/e7f5eb78-be84-41c5-945b-a0a8d0322c3b

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_P2M_OBdd_evaluate_terminal__321343d95937
import Theorems.Thm_P2M_OBdd_evaluate_node___75814e9183f4
import Theorems.Thm_OBdd_var_lt_high_var
import Theorems.Thm_OBdd_var_lt_low_var
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution (O : OBdd n m) (i : Fin O.var) :
    Nary.IndependentOf (O.evaluate) ⟨i.1, Fin.val_lt_of_le i (Fin.is_le _)⟩ := by
  cases h : O.1.root with
  | terminal _ => simp [evaluate_terminal' h]
  | node j =>
    intro b I
    rw [evaluate_node'' h]
    simp only
    rcases i with ⟨i, hi⟩
    congr 1
    · simp only [eq_iff_iff, Bool.coe_iff_coe]
      symm
      apply Vector.getElem_set_ne _ _ (Nat.ne_of_lt (by simp_all))
    · exact (solution (O.high h) ⟨i, .trans hi var_lt_high_var⟩) b I
    · exact (solution (O.low  h) ⟨i, .trans hi var_lt_low_var⟩) b I
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
end OBdd
