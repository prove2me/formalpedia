-- Prove2me | solution 1 for TwoDegenerateGraphs.binaryPinskerGap_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/f7ca8b5a-7dc5-4d26-9934-21632bd67f93

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution {q : ℝ}
    (hqzero : q ≠ 0) (hqone : q ≠ 1) :
    HasDerivAt binaryPinskerGap (binaryPinskerGapDeriv q) q := by
  have hlinear : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 q := by
    simpa using (hasDerivAt_const_mul (x := q) (2 : ℝ)).sub_const 1
  have hderiv :=
    ((Real.hasDerivAt_binEntropy hqzero hqone).const_sub (Real.log 2)).sub
      ((hlinear.pow 2).div_const 2)
  convert hderiv using 1
  all_goals
    first
    | rfl
    | (dsimp [binaryPinskerGap, binaryPinskerGapDeriv]; ring)
end TwoDegenerateGraphs
