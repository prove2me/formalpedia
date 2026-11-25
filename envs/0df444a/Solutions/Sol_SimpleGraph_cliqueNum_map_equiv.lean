-- Prove2me | solution 1 for SimpleGraph.cliqueNum_map_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:00:54.953495+00:00
-- url     : https://prove2.me/submissions/6a04640e-d6bc-4067-ba02-75ec109c71cc

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.SplitIfs
public import Definitions.Def_Erdos627_Mycielski

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
variable {V : Type*}
variable {G : SimpleGraph V} {α : Type*} {k : ℕ}
variable {W : Type*}
namespace SimpleGraph
theorem _root_.solution (G : SimpleGraph V) (e : V ≃ W) :
    (G.map e).cliqueNum = G.cliqueNum := by
  unfold cliqueNum
  congr 1
  ext n
  change ((G.map e).cliqueSet n).Nonempty ↔ (G.cliqueSet n).Nonempty
  rw [cliqueSet_map_of_equiv]
  exact Set.image_nonempty
end SimpleGraph
