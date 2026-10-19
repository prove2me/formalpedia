-- Prove2me | solution 1 for TwoDegenerateGraphs.pairCoordinatePairMismatchCount_sum_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/18dd9b77-bba5-48c7-938e-98ed1522fe5a

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinatePairMismatchCount_homogeneous

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
    (∑ pair ∈ pairTypeGroup parents coordinate 0,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 * (pairTypeGroupChildOnes parents children coordinate 0).card := by
  classical
  calc
    (∑ pair ∈ pairTypeGroup parents coordinate 0,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      ∑ pair ∈ pairTypeGroup parents coordinate 0,
        if children pair coordinate = true then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro pair hpair
        have hmembership :
            pair ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 =>
                  pairCoordinateBitType parents coordinate candidate = 0)) := by
          simpa only [pairTypeGroup] using hpair
        have hgroup := (Finset.mem_filter.mp hmembership).2
        have hterm := pairCoordinatePairMismatchCount_homogeneous
          parents children coordinate pair false hgroup
        cases hchild : children pair coordinate <;>
          simpa [hchild] using hterm
    _ = 2 * (pairTypeGroupChildOnes parents children coordinate 0).card := by
      rw [← Finset.sum_filter]
      simp [pairTypeGroupChildOnes, Nat.mul_comm]
end TwoDegenerateGraphs
