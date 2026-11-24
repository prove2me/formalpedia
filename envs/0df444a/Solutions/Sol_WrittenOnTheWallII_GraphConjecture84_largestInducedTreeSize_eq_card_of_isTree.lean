-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.largestInducedTreeSize_eq_card_of_isTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:32:18.780067+00:00
-- url     : https://prove2.me/submissions/2799cb90-719d-4969-81f4-5929ca8f604b

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_largestInducedTreeSize_le_card
public import Theorems.Thm_SimpleGraph_card_le_largestInducedTreeSize


set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.IsTree) :
    largestInducedTreeSize G = Fintype.card α := by
  apply le_antisymm (largestInducedTreeSize_le_card G)
  have ht : (G.induce (↑(Finset.univ : Finset α) : Set α)).IsTree := by
    rw [Finset.coe_univ]
    exact (G.induceUnivIso).isTree_iff.mpr hG
  simpa only [Finset.card_univ] using card_le_largestInducedTreeSize ht
end WrittenOnTheWallII.GraphConjecture84
