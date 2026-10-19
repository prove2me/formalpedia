-- Prove2me | solution 2 for SandsSauerWoodrow.asymPart_strictOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-17T23:23:47.282986+00:00
-- url     : https://prove2.me/submissions/f3fef986-82f6-422f-9834-83b04bff96a4

import Definitions.Def_opg1808_colored_tournaments
import Definitions.Def_SandsSauerWoodrow_OrderOnSets

open OPG1808
open SandsSauerWoodrow

universe u

/-- The asymmetric part of one colour's reachability is a strict partial order:
irreflexive, because its two conjuncts contradict each other, and transitive, because
reachability composes while a path back from the third vertex would compose with the
second edge of the chain to give a path back from the second. -/
theorem solution {V : Type u} (D : Digraph V) (color : ArcColoring V) (k : Fin 3) :
    Irreflexive (asymPart D color k) ∧ Transitive (asymPart D color k) := by
  constructor
  · intro x hx
    exact hx.2 hx.1
  · intro x y z hxy hyz
    refine ⟨Relation.ReflTransGen.trans hxy.1 hyz.1, fun hzx => ?_⟩
    exact hxy.2 (Relation.ReflTransGen.trans hyz.1 hzx)
