-- Prove2me | solution 1 for OBdd.high_oreachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:10:13.470417+00:00
-- url     : https://prove2.me/submissions/3f104d27-d1c0-419d-b0e8-f3336f5cf2b1

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
theorem _root_.solution {n m} {j} {O U : OBdd n m} {U_root_def : U.1.root = node j} : O.OReachable U → O.OReachable (U.high U_root_def) := fun h ↦
  Relation.ReflTransGen.tail h oedge_of_high
end OBdd
