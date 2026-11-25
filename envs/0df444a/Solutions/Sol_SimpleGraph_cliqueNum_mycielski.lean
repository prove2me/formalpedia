-- Prove2me | solution 1 for SimpleGraph.cliqueNum_mycielski
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:03:28.804536+00:00
-- url     : https://prove2.me/submissions/afa05108-f698-47e8-a798-76643ccccaa3

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.SplitIfs
public import Definitions.Def_Erdos627_Mycielski
public import Theorems.Thm_SimpleGraph_CliqueFree_cliqueNum_le_two

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
variable {V : Type*}
variable {G : SimpleGraph V} {α : Type*} {k : ℕ}
namespace SimpleGraph
theorem _root_.solution [Finite V] [Nonempty V] {G : SimpleGraph V}
    (hG : G.CliqueFree 3) : G.mycielski.cliqueNum = 2 := by
  classical
  apply Nat.le_antisymm hG.mycielski.cliqueNum_le_two
  obtain ⟨v⟩ := ‹Nonempty V›
  have hpair : G.mycielski.IsClique
      ({none, some (Sum.inr v)} : Finset (Option (V ⊕ V))) := by
    simp [mycielskiAdj]
  simpa using hpair.card_le_cliqueNum
end SimpleGraph
