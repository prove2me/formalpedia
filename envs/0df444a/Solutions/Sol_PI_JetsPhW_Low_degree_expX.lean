-- Prove2me | solution 1 for PI.JetsPhW.Low.degree_expX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:46:46.105095+00:00
-- url     : https://prove2.me/submissions/daf3793e-bec9-4d8c-8d47-dd0cf9e62ac4

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
theorem _root_.solution : Finsupp.degree E0 = 1 := Finsupp.degree_single _ _
end PI.JetsPhW.Low
