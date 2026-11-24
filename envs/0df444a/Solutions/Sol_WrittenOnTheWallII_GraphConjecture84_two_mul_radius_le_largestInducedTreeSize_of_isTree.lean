-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.two_mul_radius_le_largestInducedTreeSize_of_isTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:34:02.758464+00:00
-- url     : https://prove2.me/submissions/9732bc36-19cd-44ef-906c-c045086f03e1

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_two_mul_radius_le_card
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_largestInducedTreeSize_eq_card_of_isTree

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α}
    (hG : G.IsTree) : 2 * G.radius.toNat ≤ largestInducedTreeSize G := by
  rw [largestInducedTreeSize_eq_card_of_isTree hG]
  exact two_mul_radius_le_card hG.connected
end WrittenOnTheWallII.GraphConjecture84
