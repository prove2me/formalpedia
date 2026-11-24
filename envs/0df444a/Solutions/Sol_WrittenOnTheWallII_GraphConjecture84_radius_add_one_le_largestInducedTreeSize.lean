-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.radius_add_one_le_largestInducedTreeSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:28:37.017811+00:00
-- url     : https://prove2.me/submissions/2e7eb82c-3ef8-4b43-82d5-d859a8de8598

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_one_le_largestInducedTreeSize

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α}
    [Nonempty α] (h : G.Connected) :
    G.radius.toNat + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_radius_of_finite
  have hd : G.dist u v = G.radius.toNat := congrArg ENat.toNat huv
  rw [← hd]
  exact dist_add_one_le_largestInducedTreeSize (h u v)
end WrittenOnTheWallII.GraphConjecture84
