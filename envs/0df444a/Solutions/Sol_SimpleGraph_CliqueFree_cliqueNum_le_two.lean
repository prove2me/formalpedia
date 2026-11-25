-- Prove2me | solution 1 for SimpleGraph.CliqueFree.cliqueNum_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:00:19.952691+00:00
-- url     : https://prove2.me/submissions/d04f9fb9-28cd-4188-a78d-92d2d860dac5

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
namespace SimpleGraph
namespace CliqueFree
theorem _root_.solution {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    G.cliqueNum ≤ 2 := by
  by_contra h
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  exact (CliqueFree.mono (by omega : 3 ≤ G.cliqueNum) hG) s hs
end CliqueFree
end SimpleGraph
