-- Prove2me | solution 1 for PI.VolStabSW.densInf_of_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:23.621859+00:00
-- url     : https://prove2.me/submissions/6ca9dea5-816d-4507-8bb8-9951ae6e9245

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfCV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfTop
import Theorems.Thm_PI_VolStabSW_submDens_holds
import Theorems.Thm_PI_VolStabSW_densInf_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
namespace PI.VolStabSW
theorem _root_.solution (h : CoordInf) : DensInf := densInf_of submDens_holds h
end PI.VolStabSW
