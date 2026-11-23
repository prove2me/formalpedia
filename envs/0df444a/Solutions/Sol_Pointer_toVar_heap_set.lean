-- Prove2me | solution 1 for Pointer.toVar_heap_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:02:02.468548+00:00
-- url     : https://prove2.me/submissions/ed600699-7566-4e99-9aa7-d3d72794b462

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
theorem _root_.solution {i j : Fin n} : i ≠ j → (toVar (M.set i N) (node j)).1 = (toVar M (node j)).1 := by
  intro neq
  simp only [Nat.succ_eq_add_one, toVar_node_eq]
  congr 2
  apply Vector.getElem_set_ne
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  simp_all
end Pointer
