-- Prove2me | solution 1 for TwoDegenerateGraphs.sum_pairCoordinatePairMismatchCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/e79d9dd0-a5e5-4b6a-9e75-6cb60c81654e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinatePairMismatchCount_sum_false
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinatePairMismatchCount_sum_true
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinatePairMismatchCount_sum_mixed

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
    (∑ pair : PairLayer parentCount 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 * (pairTypeGroupChildOnes parents children coordinate 0).card +
      (pairTypeGroup parents coordinate 2).card +
      2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by
  classical
  have hmaps :
      (((Finset.univ : Finset (PairLayer parentCount 1)) :
        Set (PairLayer parentCount 1))).MapsTo
          (pairCoordinateBitType parents coordinate)
          (Finset.univ : Finset PairBitType) := by
    intro pair _
    exact Finset.mem_univ _
  have hfiber :=
    (Finset.sum_fiberwise_of_maps_to hmaps
      (fun pair =>
        pairCoordinatePairMismatchCount
          parents children coordinate pair)).symm
  have hpartition :
      (∑ pair : PairLayer parentCount 1,
        pairCoordinatePairMismatchCount
          parents children coordinate pair) =
        (∑ pair ∈ pairTypeGroup parents coordinate 0,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) +
        (∑ pair ∈ pairTypeGroup parents coordinate 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) +
        (∑ pair ∈ pairTypeGroup parents coordinate 2,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) := by
    simpa [pairTypeGroup, Fin.sum_univ_succ, add_assoc] using hfiber
  rw [pairCoordinatePairMismatchCount_sum_false,
    pairCoordinatePairMismatchCount_sum_true,
    pairCoordinatePairMismatchCount_sum_mixed] at hpartition
  omega
end TwoDegenerateGraphs
