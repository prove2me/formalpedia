-- Prove2me | solution 1 for PI.JetsPhW.Low.expX_ne_expY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:47:01.074891+00:00
-- url     : https://prove2.me/submissions/13cc74dc-9392-4629-8fe2-e31f5cbf13b6

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
theorem _root_.solution : E0 ≠ E1 := by
  intro h
  have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
  simp at this
end PI.JetsPhW.Low
