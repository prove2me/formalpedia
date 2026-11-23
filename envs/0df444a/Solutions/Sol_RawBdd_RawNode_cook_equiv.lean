-- Prove2me | solution 1 for RawBdd.RawNode.cook_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:58:09.468337+00:00
-- url     : https://prove2.me/submissions/1fe69e4b-3b26-4eff-83bd-343eac37f331

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_RawBdd_RawPointer_cook_equiv
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
open RawBdd
namespace RawBdd
namespace RawNode
theorem _root_.solution : Node.equiv (RawNode.cook N h1) (RawNode.cook N h2) := by
  simp only [Node.equiv]
  constructor
  · rfl
  · rcases h1 with ⟨h11, h12⟩
    rcases h2 with ⟨h21, h22⟩
    constructor
    · apply RawPointer.cook_equiv <;> assumption
    · apply RawPointer.cook_equiv <;> assumption
end RawNode
end RawBdd
