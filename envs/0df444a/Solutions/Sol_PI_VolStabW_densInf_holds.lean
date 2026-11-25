-- Prove2me | solution 1 for PI.VolStabW.densInf_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:30:22.812118+00:00
-- url     : https://prove2.me/submissions/62200989-d6ed-457e-b509-c6bc7359eea0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfTR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfAll
import Theorems.Thm_PI_VolStabW_tensR_holds
import Theorems.Thm_PI_VolStabW_densInf_of_tensR


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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct
open PI.AdicCompletionValuation
namespace PI.VolStabW
theorem _root_.solution : DensInf := densInf_of_tensR tensR_holds
end PI.VolStabW
