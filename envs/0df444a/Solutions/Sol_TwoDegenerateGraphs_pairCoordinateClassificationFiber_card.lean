-- Prove2me | solution 1 for TwoDegenerateGraphs.pairCoordinateClassificationFiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/d98ab46c-2c00-4bda-8523-9bb5976294b5

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
    (bitType : PairBitType) (coordinate : Fin dimension) :
    Fintype.card
      (ClassificationFiber
        (pairCoordinateClassification parents) (bitType, coordinate)) =
      (pairTypeGroup parents coordinate bitType).card := by
  calc
    Fintype.card
        (ClassificationFiber
          (pairCoordinateClassification parents) (bitType, coordinate)) =
        Fintype.card ↥(pairTypeGroup parents coordinate bitType) :=
      Fintype.card_congr
        (pairCoordinateClassificationFiberEquiv parents bitType coordinate)
    _ = (pairTypeGroup parents coordinate bitType).card :=
      Fintype.card_coe _
end TwoDegenerateGraphs
