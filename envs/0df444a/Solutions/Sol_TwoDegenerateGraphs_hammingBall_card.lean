-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingBall_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/67ab21b3-264d-420d-a72e-afc7272f8bb4

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_boundedDifferenceSets_card

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (dimension radius : ℕ)
    (u : HammingWord dimension) :
    (hammingBall dimension radius u).card =
      ∑ d ∈ Finset.range (radius + 1), dimension.choose d := by
  calc
    (hammingBall dimension radius u).card =
        Fintype.card ↥(hammingBall dimension radius u) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card ↥(boundedDifferenceSets dimension radius) :=
      Fintype.card_congr (hammingBallEquiv dimension radius u)
    _ = (boundedDifferenceSets dimension radius).card :=
      Fintype.card_coe _
    _ = ∑ d ∈ Finset.range (radius + 1), dimension.choose d :=
      boundedDifferenceSets_card dimension radius
end TwoDegenerateGraphs
