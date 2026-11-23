-- Prove2me | solution 1 for P2M_OBdd_card_reachable_node__da57529a8d4b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:05:27.259135+00:00
-- url     : https://prove2.me/submissions/248c3a57-f5a5-446b-bba0-5ff527fee78a

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_P2M_OBdd_reachable_from_node_iff__59148aa8fc2a

set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} (h : O.1.root = node j) :
  Fintype.card {p // Reachable O.1.heap O.1.root p} =
  Fintype.card {p // p = O.1.root ∨ (Reachable O.1.heap (O.low  h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p)} := by
  refine Fintype.card_congr' ?_
  conv =>
    lhs
    arg 1
    ext
    rw [reachable_from_node_iff' h]
end OBdd
