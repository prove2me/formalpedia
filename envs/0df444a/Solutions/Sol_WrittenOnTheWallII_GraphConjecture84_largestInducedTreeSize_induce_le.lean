-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.largestInducedTreeSize_induce_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:33:14.106874+00:00
-- url     : https://prove2.me/submissions/132e3ed6-b204-4231-a401-a00813f28a8b

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_largestInducedTreeSize_le_of_embedding

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution (G : SimpleGraph α) (S : Set α)
    [DecidablePred (· ∈ S)] :
    largestInducedTreeSize (G.induce S) ≤ largestInducedTreeSize G :=
  largestInducedTreeSize_le_of_embedding (SimpleGraph.Embedding.induce S)
end WrittenOnTheWallII.GraphConjecture84
