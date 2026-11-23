-- Prove2me | solution 1 for P2M_OBdd_toTree_terminal__6f80b985dd51
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:55:21.864081+00:00
-- url     : https://prove2.me/submissions/4bb5c231-598a-473f-a4d5-f3cdab3b9fad

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
theorem _root_.solution {n m} {O : OBdd n m} : O.1.root = terminal b → O.toTree = .leaf b := by
  intro h
  rcases O with ⟨⟨heap, root⟩, ho⟩
  simp_all
end OBdd
