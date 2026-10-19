-- Prove2me | solution 1 for TwoDegenerateGraphs.binaryPinskerGapDeriv_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/5535cba4-5d88-43f4-a60b-7e304c91b7bf

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution {q : ℝ}
    (hqzero : q ≠ 0) (hqone : q ≠ 1) :
    HasDerivAt binaryPinskerGapDeriv (binaryPinskerGapDerivTwo q) q := by
  have hlinear : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 q := by
    simpa using (hasDerivAt_const_mul (x := q) (2 : ℝ)).sub_const 1
  have hcomplement : HasDerivAt (fun x : ℝ => 1 - x) (-1) q := by
    simpa using (hasDerivAt_id q).const_sub 1
  have hcomplement_ne : 1 - q ≠ 0 := sub_ne_zero.mpr hqone.symm
  have hderiv :=
    ((Real.hasDerivAt_log hqzero).sub
      (hcomplement.log hcomplement_ne)).sub (hlinear.const_mul 2)
  convert hderiv using 1
  all_goals
    first
    | rfl
    | (dsimp [binaryPinskerGapDeriv, binaryPinskerGapDerivTwo]; ring)
end TwoDegenerateGraphs
