-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.T.rpow_neg_le_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:50.995199+00:00
-- url     : https://prove2.me/submissions/a4b499f6-5ff2-4136-a861-cdd13360f90a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousHerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.T
theorem _root_.solution (x a a0 d : ℝ) (hx : 0 < x) (ha : |a - a0| ≤ d) :
    x ^ (-a) ≤ x ^ (-(a0 - d)) + x ^ (-(a0 + d)) := by
  obtain ⟨ha1, ha2⟩ := abs_le.1 ha
  have p1 := Real.rpow_pos_of_pos hx (-(a0 - d))
  have p2 := Real.rpow_pos_of_pos hx (-(a0 + d))
  rcases le_or_gt 1 x with h1 | h1
  · have : x ^ (-a) ≤ x ^ (-(a0 - d)) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    linarith
  · have : x ^ (-a) ≤ x ^ (-(a0 + d)) := Real.rpow_le_rpow_of_exponent_ge hx h1.le (by linarith)
    linarith
end PositivityTheory.Rg.Sw.WR.T
