-- Prove2me | solution 1 for OBdd.ordered_of_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:02:32.006383+00:00
-- url     : https://prove2.me/submissions/976c924f-be97-4e48-9f98-3f0da0db1f0a

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
theorem _root_.solution {O : OBdd n m} {h : O.1.heap = v} {r : O.1.root = q} (p) : Edge v q p → Bdd.Ordered {heap := v, root := p} := by
  rw [← h]
  rw [← r]
  intro e
  exact ordered_of_relevant O ⟨p, reachable_of_edge e⟩
end OBdd
