-- Prove2me | solution 1 for P2M_Pointer_toVar_heap_set__d9257dfabaf5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:02:40.313258+00:00
-- url     : https://prove2.me/submissions/c9236498-6e8f-4571-bda9-b6694ff3b6d6

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_Pointer_toVar_heap_set
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
namespace Pointer
theorem _root_.solution {i j : Fin n} : i ≠ j → (toVar (M.set i N) (node j)) = (toVar M (node j)) := by
  intro neq
  simp only [Nat.succ_eq_add_one]
  apply Fin.eq_of_val_eq
  exact toVar_heap_set neq
end Pointer
