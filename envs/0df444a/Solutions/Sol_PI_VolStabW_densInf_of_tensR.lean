-- Prove2me | solution 1 for PI.VolStabW.densInf_of_tensR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:36.63469+00:00
-- url     : https://prove2.me/submissions/cebd2984-f4fb-4425-83b7-40a3ba492efd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfSS
import Theorems.Thm_PI_VolStabW_semisimpleTens_holds
import Theorems.Thm_PI_VolStabW_densInf_of_ss


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
namespace PI.VolStabW
theorem _root_.solution (h : TensR) : DensInf := densInf_of_ss h semisimpleTens_holds
end PI.VolStabW
