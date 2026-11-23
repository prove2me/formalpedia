-- Prove2me | solution 1 for PI.JetsPhW.Low.expXY_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:03.226306+00:00
-- url     : https://prove2.me/submissions/5dcdc431-e53a-4b2e-b7fa-a69281a82729

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.Low
variable {K : Type*} [CommRing K]
namespace PI.JetsPhW.Low
theorem _root_.solution : bivariateExponentMonomial ≠ 0 := by
  intro h
  have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
  simp at this
end PI.JetsPhW.Low
