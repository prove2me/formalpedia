-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.dist_add_one_le_largestInducedTreeSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:26:12.441896+00:00
-- url     : https://prove2.me/submissions/d3bf90d5-779c-4d43-b60f-9e669c208083

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_SimpleGraph_Walk_induce_support_isTree_of_length_eq_dist
public import Theorems.Thm_SimpleGraph_card_le_largestInducedTreeSize


set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} {u v : α}
    (h : G.Reachable u v) : G.dist u v + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨p, hp, hlen⟩ := h.exists_path_of_dist
  have hcard : p.support.toFinset.card = G.dist u v + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support, hlen]
  rw [← hcard]
  exact card_le_largestInducedTreeSize (p.induce_support_isTree_of_length_eq_dist hlen)
end WrittenOnTheWallII.GraphConjecture84
