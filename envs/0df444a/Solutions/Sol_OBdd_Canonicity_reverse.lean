-- Prove2me | solution 1 for OBdd.Canonicity_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:03:12.654803+00:00
-- url     : https://prove2.me/submissions/f28aab7d-e95b-4636-9d1c-17c1743966c8

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
theorem _root_.solution {O : OBdd n m} {U : OBdd n m'}:
    O.HSimilar U → O.evaluate = U.evaluate := by
  simp_all [evaluate, Function.comp_apply, HSimilar]
end OBdd
