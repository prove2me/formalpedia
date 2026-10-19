-- Prove2me | solution 1 for TwoDegenerateGraphs.pairCoordinateKernel_empiricalConditionalEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/a5b6e6eb-730d-4e1e-a91c-1bf9dd24c93e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinateKernel_childProbability
import Theorems.Thm_TwoDegenerateGraphs_withoutReplacementBinaryPairMass_eq_pairTypeGroup

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalConditionalEntropy parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      pairCoordinateConditionalEntropy parents children coordinate := by
  unfold empiricalConditionalEntropy
    withoutReplacementBinaryPairExpectation
  simp_rw [withoutReplacementBinaryPairMass_eq_pairTypeGroup
    hparents parents coordinate]
  simp [Fintype.univ_bool,
    pairCoordinateKernel_childProbability,
    pairBitTypeOfOutcomes,
    pairCoordinateConditionalEntropy,
    Fin.sum_univ_succ]
  ring
end TwoDegenerateGraphs
