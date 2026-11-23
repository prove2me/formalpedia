-- Prove2me | solution 1 for Pointer.MayPrecede_node_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:59:51.752115+00:00
-- url     : https://prove2.me/submissions/0e705021-a250-4812-aead-61474e0ecc6e

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
namespace Pointer
theorem _root_.solution {n m} (w : Vector (Node n m) m) {j} : MayPrecede w (node j) (terminal b) := by
  simp only [MayPrecede, Nat.succ_eq_add_one, toVar, Fin.getElem_fin]
  refine Fin.mk_lt_of_lt_val ?_
  simp only [Fin.val_last, Fin.is_lt]
end Pointer
