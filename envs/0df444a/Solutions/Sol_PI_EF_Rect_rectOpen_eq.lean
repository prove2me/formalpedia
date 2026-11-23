-- Prove2me | solution 1 for PI.EF.Rect.rectOpen_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:14.153544+00:00
-- url     : https://prove2.me/submissions/fd5985f7-2c70-43ec-9479-e03023db09dc

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
theorem _root_.solution (z w : ℂ) : rectOpen z w = Ioo z.re w.re ×ℂ Ioo z.im w.im := by
  ext s
  simp [rectOpen, Complex.mem_reProdIm, and_assoc]
end PI.EF.Rect
