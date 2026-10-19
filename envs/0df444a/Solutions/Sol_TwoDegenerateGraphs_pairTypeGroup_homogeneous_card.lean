-- Prove2me | solution 1 for TwoDegenerateGraphs.pairTypeGroup_homogeneous_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/b59103fc-6385-4dff-bb66-daa850a9f7b8

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
    (coordinate : Fin dimension)
    (outcome : Bool) :
    (pairTypeGroup parents coordinate
      (if outcome then (1 : PairBitType) else 0)).card =
      (pairParentCoordinateSupport parents coordinate outcome).card.choose 2 := by
  calc
    (pairTypeGroup parents coordinate
      (if outcome then (1 : PairBitType) else 0)).card =
      Fintype.card
        ↥(pairTypeGroup parents coordinate
          (if outcome then (1 : PairBitType) else 0)) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
      ↥((pairParentCoordinateSupport parents coordinate outcome).powersetCard 2) :=
      Fintype.card_congr
        (pairTypeGroupHomogeneousEquiv parents coordinate outcome)
    _ = ((pairParentCoordinateSupport parents coordinate outcome).powersetCard 2).card :=
      Fintype.card_coe _
    _ = (pairParentCoordinateSupport parents coordinate outcome).card.choose 2 :=
      Finset.card_powersetCard _ _
end TwoDegenerateGraphs
