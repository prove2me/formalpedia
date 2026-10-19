-- Prove2me | solution 1 for TwoDegenerateGraphs.pairCoordinatePairMismatchCount_sum_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/5a4998ab-304d-4925-b1eb-834f8070dfdc

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
    (∑ pair ∈ pairTypeGroup parents coordinate 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by
  classical
  let zeroChildren : Finset (PairLayer parentCount 1) :=
    (pairTypeGroup parents coordinate 1).filter
      (fun pair => children pair coordinate = false)
  have hpartition :
      (pairTypeGroupChildOnes parents children coordinate 1).card +
        zeroChildren.card =
          (pairTypeGroup parents coordinate 1).card := by
    have hfilter := Finset.card_filter_add_card_filter_not
      (s := pairTypeGroup parents coordinate 1)
      (fun pair => children pair coordinate = true)
    simpa [pairTypeGroupChildOnes, zeroChildren] using hfilter
  have hzero_card :
      zeroChildren.card =
        (pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card := by
    omega
  calc
    (∑ pair ∈ pairTypeGroup parents coordinate 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      ∑ pair ∈ pairTypeGroup parents coordinate 1,
        if children pair coordinate = false then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro pair hpair
        have hmembership :
            pair ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 =>
                  pairCoordinateBitType parents coordinate candidate = 1)) := by
          simpa only [pairTypeGroup] using hpair
        have hgroup := (Finset.mem_filter.mp hmembership).2
        have hterm := pairCoordinatePairMismatchCount_homogeneous
          parents children coordinate pair true hgroup
        cases hchild : children pair coordinate <;>
          simpa [hchild] using hterm
    _ = 2 * zeroChildren.card := by
      rw [← Finset.sum_filter]
      simp [zeroChildren, Nat.mul_comm]
    _ = 2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by
      rw [hzero_card]
end TwoDegenerateGraphs
