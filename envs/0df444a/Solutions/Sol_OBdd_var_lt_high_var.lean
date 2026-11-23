-- Prove2me | solution 1 for OBdd.var_lt_high_var
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:55:20.402477+00:00
-- url     : https://prove2.me/submissions/e8b4f755-c726-4d78-b6ec-edc14bbebe3a

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
theorem _root_.solution {O : OBdd n m} {h : O.1.root = node j} :
    O.var < (O.high h).var := by
  have e := Bdd.edge_of_high (h := h) O.1
  exact @O.2 O.1.toRelevantPointer ⟨(O.high h).1.root, reachable_of_edge e⟩ e
end OBdd
