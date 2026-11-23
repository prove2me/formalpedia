-- Prove2me | solution 1 for OBdd.low_oreachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:10:10.752987+00:00
-- url     : https://prove2.me/submissions/2a00a0be-b22e-4e13-a42a-dc4a50767528

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
theorem _root_.solution {n m} {j} {O U : OBdd n m} {U_root_def : U.1.root = node j}: O.OReachable U → O.OReachable (U.low U_root_def) := fun h ↦
  Relation.ReflTransGen.tail h oedge_of_low
end OBdd
