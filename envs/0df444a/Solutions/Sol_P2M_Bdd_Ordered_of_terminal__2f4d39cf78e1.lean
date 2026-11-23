-- Prove2me | solution 1 for P2M_Bdd_Ordered_of_terminal__2f4d39cf78e1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:02:03.287241+00:00
-- url     : https://prove2.me/submissions/f5f19f54-8190-4f93-ae31-f923a8670ca1

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
namespace Bdd
theorem _root_.solution {B : Bdd n m} : B.root = terminal b → B.Ordered := by
  intro h
  rcases B with ⟨M, r⟩
  simp only at h
  rw [h]
  apply Ordered_of_terminal
end Bdd
