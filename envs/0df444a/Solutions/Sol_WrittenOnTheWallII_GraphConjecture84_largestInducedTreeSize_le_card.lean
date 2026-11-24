-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.largestInducedTreeSize_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:26:20.673852+00:00
-- url     : https://prove2.me/submissions/572f68d8-14d5-4145-a09f-e7458262d6d2

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution (G : SimpleGraph α) :
    largestInducedTreeSize G ≤ Fintype.card α := by
  apply csSup_le'
  rintro n ⟨s, rfl, _⟩
  exact Finset.card_le_univ s
end WrittenOnTheWallII.GraphConjecture84
