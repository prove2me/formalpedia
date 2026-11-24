-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.conjecture84
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:45:51.482788+00:00
-- url     : https://prove2.me/submissions/cb171bf3-f0ba-44f2-b655-83156be679f6

module
public import Definitions.Def_Wowii84_Main
public import Definitions.Def_Wowii84_Solution
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_conjecture84_proof


set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hδ : 0 < G.minDegree) :
    2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (largestInducedTreeSize G : ℝ) :=
  conjecture84_proof G h hδ
end WrittenOnTheWallII.GraphConjecture84
