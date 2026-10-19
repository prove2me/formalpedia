-- Prove2me | solution 1 for TwoDegenerateGraphs.pairCoordinateConditionalEntropy_empirical_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/e079ff19-3ad0-4380-8e8c-c1ba8be71626

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_empiricalConditionalEntropy_bound
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinateKernel_parentProbability
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinateKernel_empiricalConditionalEntropy
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinateKernel_empiricalChildMarginal

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    pairCoordinateConditionalEntropy parents children coordinate ≤
      kappa +
        logTwo 3 *
          empiricalAverageDisagreement parentCount
            (pairParentCoordinateOneCount parents coordinate)
            (pairCoordinateKernel (by omega)
              parents children coordinate) +
        (binaryEntropy
            ((pairChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 2 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2 +
        empiricalEntropyError parentCount := by
  have hones := pairParentCoordinateOneCount_le parents coordinate
  let kernel : BinaryPairKernel :=
    pairCoordinateKernel (by omega) parents children coordinate
  have hkernel := empiricalConditionalEntropy_bound
    parentCount (pairParentCoordinateOneCount parents coordinate)
      hparents hones kernel
      (pairCoordinateKernel_parentProbability
        (by omega) parents children coordinate)
  change
    empiricalConditionalEntropy parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega)
          parents children coordinate) ≤ _ at hkernel
  rw [pairCoordinateKernel_empiricalConditionalEntropy
    (by omega) parents children coordinate] at hkernel
  rw [pairCoordinateKernel_empiricalChildMarginal
    (by omega) parents children coordinate] at hkernel
  change
    pairCoordinateConditionalEntropy parents children coordinate ≤
      kappa +
        logTwo 3 *
          empiricalAverageDisagreement parentCount
            (pairParentCoordinateOneCount parents coordinate)
            (pairCoordinateKernel (by omega)
              parents children coordinate) +
        (binaryEntropy
            ((pairChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 2 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2 +
        empiricalEntropyError parentCount at hkernel
  exact hkernel
end TwoDegenerateGraphs
