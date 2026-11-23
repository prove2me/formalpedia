-- Prove2me | solution 1 for OBdd.evaluate_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:09:35.30778+00:00
-- url     : https://prove2.me/submissions/a8475d2e-a88d-47d8-8d13-5d5cac239054

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic

set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} (h : n = n') : (h ▸ O).evaluate I = O.evaluate (h ▸ I) := by
  subst h
  rfl
end OBdd
