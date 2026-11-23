-- Prove2me | solution 1 for OBdd.HSimilar_of_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:09:44.162795+00:00
-- url     : https://prove2.me/submissions/9cd33c37-bcc3-45eb-9bca-9b32ddcb1b40

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_P2M_OBdd_toTree_terminal__6f80b985dd51
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {n m m' : Nat} {b : Bool} {O : OBdd n m} {U : OBdd n m'} :
    O.1.root = terminal b → U.1.root = terminal b → O.HSimilar U := by
  intro h1 h2
  simp [HSimilar]
  rw [toTree_terminal' h1, toTree_terminal' h2]
end OBdd
