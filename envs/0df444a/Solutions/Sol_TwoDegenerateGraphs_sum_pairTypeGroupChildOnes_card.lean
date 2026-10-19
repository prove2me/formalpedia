-- Prove2me | solution 1 for TwoDegenerateGraphs.sum_pairTypeGroupChildOnes_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/aa87bf24-f1b2-4393-826f-50a27c2a35c1

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : PairBitType,
      (pairTypeGroupChildOnes parents children coordinate bitType).card) =
      pairChildCoordinateOneCount children coordinate := by
  classical
  let support : Finset (PairLayer parentCount 1) :=
    booleanWordOnes (fun pair => children pair coordinate)
  have hmaps :
      ((support : Finset (PairLayer parentCount 1)) :
        Set (PairLayer parentCount 1)).MapsTo
          (pairCoordinateBitType parents coordinate)
          (Finset.univ : Finset PairBitType) := by
    intro pair _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (bitType : PairBitType) :
      support.filter
        (fun pair => pairCoordinateBitType parents coordinate pair = bitType) =
      pairTypeGroupChildOnes parents children coordinate bitType := by
    ext pair
    simp [support, booleanWordOnes,
      pairTypeGroupChildOnes, pairTypeGroup, and_comm]
  calc
    (∑ bitType : PairBitType,
      (pairTypeGroupChildOnes parents children coordinate bitType).card) =
      ∑ bitType : PairBitType,
        (support.filter
          (fun pair =>
            pairCoordinateBitType parents coordinate pair = bitType)).card := by
          apply Finset.sum_congr rfl
          intro bitType _
          rw [hfiber]
    _ = support.card := by
      exact hpartition.symm
    _ = pairChildCoordinateOneCount children coordinate := by
      rfl
end TwoDegenerateGraphs
