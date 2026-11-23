-- Prove2me | solution 1 for RawBdd.RawPointer.cook_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:05:46.174009+00:00
-- url     : https://prove2.me/submissions/7c846672-9c7d-4773-af66-9b21c5df7a06

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
open RawBdd
namespace RawBdd
namespace RawPointer
theorem _root_.solution {p : RawPointer} {h1 h2 : p.Bounded m} : p.cook h1 = p.cook h2 := by
  cases p with
  | inl _ => rfl
  | inr i => exact congrArg Pointer.node (Fin.ext rfl)
end RawPointer
end RawBdd
