-- Prove2me | solution 1 for OBdd.low_root_eq_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:58:46.884583+00:00
-- url     : https://prove2.me/submissions/7ba23a39-162d-4e00-a3a2-8d54742599e0

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
theorem _root_.solution {O : OBdd n m} {h : O.1.root = node j} : (O.low h).1.root = O.1.heap[j].low := rfl
end OBdd
