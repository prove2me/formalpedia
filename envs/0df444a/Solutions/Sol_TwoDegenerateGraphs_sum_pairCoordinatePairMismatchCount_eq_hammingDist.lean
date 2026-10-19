-- Prove2me | solution 1 for TwoDegenerateGraphs.sum_pairCoordinatePairMismatchCount_eq_hammingDist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/fd996c33-798e-47d2-9eea-ff0d37ac43a5

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
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    (∑ coordinate : Fin dimension,
      ∑ pair : PairLayer parentCount 1,
        pairCoordinatePairMismatchCount
          parents children coordinate pair) =
      ∑ pair : PairLayer parentCount 1,
        ∑ parent ∈ pair.val,
          hammingDist (parents parent) (children pair) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro pair _
  have hcount (coordinate : Fin dimension) :
      pairCoordinatePairMismatchCount parents children coordinate pair =
        ∑ parent ∈ pair.val,
          if parents parent coordinate ≠ children pair coordinate
            then 1 else 0 := by
    change
      (pair.val.filter
        (fun parent =>
          parents parent coordinate ≠ children pair coordinate)).card = _
    exact (Finset.sum_boole _ _).symm
  simp_rw [hcount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro parent _
  change
    (∑ coordinate : Fin dimension,
      if parents parent coordinate ≠ children pair coordinate
        then 1 else 0) =
      ((Finset.univ : Finset (Fin dimension)).filter
        (fun coordinate =>
          parents parent coordinate ≠ children pair coordinate)).card
  exact Finset.sum_boole _ _
end TwoDegenerateGraphs
