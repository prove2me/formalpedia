-- Prove2me | solution 1 for TwoDegenerateGraphs.pairCoordinatePairMismatchCount_sum_mixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/9bb65422-ebb6-48c2-ab22-16dee243d028

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinatePairMismatchCount_mixed

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
    (∑ pair ∈ pairTypeGroup parents coordinate 2,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      (pairTypeGroup parents coordinate 2).card := by
  classical
  calc
    (∑ pair ∈ pairTypeGroup parents coordinate 2,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      ∑ _pair ∈ pairTypeGroup parents coordinate 2, 1 := by
        apply Finset.sum_congr rfl
        intro pair hpair
        have hmembership :
            pair ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 =>
                  pairCoordinateBitType parents coordinate candidate = 2)) := by
          simpa only [pairTypeGroup] using hpair
        exact pairCoordinatePairMismatchCount_mixed
          parents children coordinate pair
            (Finset.mem_filter.mp hmembership).2
    _ = (pairTypeGroup parents coordinate 2).card := by
      simp
end TwoDegenerateGraphs
