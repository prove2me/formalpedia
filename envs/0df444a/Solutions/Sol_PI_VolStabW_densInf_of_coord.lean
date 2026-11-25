-- Prove2me | solution 1 for PI.VolStabW.densInf_of_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:30.920066+00:00
-- url     : https://prove2.me/submissions/76c2a298-71f7-4d87-b5ed-e0fad26411bb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfCV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfTop
import Theorems.Thm_PI_VolStabW_submDens_holds
import Theorems.Thm_PI_VolStabW_densInf_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
namespace PI.VolStabW
theorem _root_.solution (h : CoordInf) : DensInf := densInf_of submDens_holds h
end PI.VolStabW
