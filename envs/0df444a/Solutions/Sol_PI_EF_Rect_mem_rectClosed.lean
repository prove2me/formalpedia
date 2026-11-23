-- Prove2me | solution 1 for PI.EF.Rect.mem_rectClosed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:13.79764+00:00
-- url     : https://prove2.me/submissions/b5caef4e-4aee-4e0a-a52e-b012b52337de

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Rect
open Complex MeasureTheory intervalIntegral Set Filter Topology Real
namespace PI.EF.Rect
theorem _root_.solution {z w s : ℂ} :
    s ∈ rectClosed z w ↔ (z.re ≤ s.re ∧ s.re ≤ w.re) ∧ (z.im ≤ s.im ∧ s.im ≤ w.im) := by
  simp [rectClosed, Complex.mem_reProdIm]
end PI.EF.Rect
