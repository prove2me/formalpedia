-- Prove2me | solution 1 for Pointer.equiv_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:05:38.181785+00:00
-- url     : https://prove2.me/submissions/72571ba4-0bc6-4518-ba05-7b1d7f52c5ab

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
namespace Pointer
theorem _root_.solution (p : Pointer m) : p.equiv p := by
  simp only [Pointer.equiv]
  constructor
  · intro b hb
    exact hb
  · intro j hj
    use j
end Pointer
