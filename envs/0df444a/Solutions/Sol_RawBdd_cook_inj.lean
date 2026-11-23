-- Prove2me | solution 1 for RawBdd.cook_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:58:18.988475+00:00
-- url     : https://prove2.me/submissions/526ae7a9-9d8c-49fd-9137-a2f2edb94018

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
open RawBdd
namespace RawBdd
theorem _root_.solution {p q : RawPointer} {hp} {hq} : p.cook (m := m) hp = q.cook hq → p = q := by
  intro h
  cases p <;> cases q <;> simp_all [RawPointer.cook] <;> rfl
end RawBdd
