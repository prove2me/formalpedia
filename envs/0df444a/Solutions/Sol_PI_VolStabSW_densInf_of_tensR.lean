-- Prove2me | solution 1 for PI.VolStabSW.densInf_of_tensR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:21:50.598495+00:00
-- url     : https://prove2.me/submissions/28e39381-9e9e-498b-b632-d4be8b5c9b18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfSS
import Theorems.Thm_PI_VolStabSW_semisimpleTens_holds
import Theorems.Thm_PI_VolStabSW_densInf_of_ss


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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution (h : TensR) : DensInf := densInf_of_ss h semisimpleTens_holds
end PI.VolStabSW
