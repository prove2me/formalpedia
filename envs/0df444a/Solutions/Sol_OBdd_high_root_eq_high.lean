-- Prove2me | solution 1 for OBdd.high_root_eq_high
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:58:47.364817+00:00
-- url     : https://prove2.me/submissions/9e4c9840-263c-43a5-9d77-5d1260158c3b

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
theorem _root_.solution {O : OBdd n m} {h : O.1.root = node j} : (O.high h).1.root = O.1.heap[j].high := rfl
end OBdd
