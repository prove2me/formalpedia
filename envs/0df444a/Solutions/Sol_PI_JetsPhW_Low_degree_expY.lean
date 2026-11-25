-- Prove2me | solution 1 for PI.JetsPhW.Low.degree_expY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:46:50.462896+00:00
-- url     : https://prove2.me/submissions/39d3a29e-64d2-40f3-a90a-fd80d146d759

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
theorem _root_.solution : Finsupp.degree E1 = 1 := Finsupp.degree_single _ _
end PI.JetsPhW.Low
