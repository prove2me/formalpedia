-- Prove2me | solution 1 for PI.VolStabW.submDens_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:25:37.983083+00:00
-- url     : https://prove2.me/submissions/b3adb3b3-0bf5-4a45-852e-54194e69d7b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfLoc
import Theorems.Thm_PI_VolStabW_densAll_of_local


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
open MeasureTheory Topology
namespace PI.VolStabW
theorem _root_.solution (h : SubmLocal) : SubmDens := by
  intro n m μ ν hμ hν f hf
  exact densAll_of_local fun x hx => h n m μ ν hμ hν f hf x hx
end PI.VolStabW
