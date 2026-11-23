-- Prove2me | solution 1 for OBdd.var_lt_low_var
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:55:20.981571+00:00
-- url     : https://prove2.me/submissions/74eaff85-07e6-47da-a945-d46f7383305e

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
    O.var < (O.low h).var := by
  have e := Bdd.edge_of_low (h := h) O.1
  exact @O.2 O.1.toRelevantPointer ⟨(O.low h).1.root, reachable_of_edge e⟩ e
end OBdd
