-- Prove2me | solution 1 for SandsSauerWoodrow.asymPart_strictOrder
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:19:47.313981+00:00
-- url     : https://prove2.me/submissions/6ee95ede-fccd-4be5-8e93-8a6c0e09be5e

import Definitions.Def_opg1808_colored_tournaments
import Definitions.Def_SandsSauerWoodrow_OrderOnSets

open OPG1808

universe u
open SandsSauerWoodrow

theorem solution{V : Type u} (D : Digraph V) (color : ArcColoring V) (k : Fin 3) :
    Irreflexive (asymPart D color k) ∧ Transitive (asymPart D color k) := by
  refine ⟨fun x h => h.2 h.1, fun x y z hxy hyz => ⟨?_, fun hzx => hxy.2 ?_⟩⟩
  · exact Relation.ReflTransGen.trans hxy.1 hyz.1
  · exact Relation.ReflTransGen.trans hyz.1 hzx
