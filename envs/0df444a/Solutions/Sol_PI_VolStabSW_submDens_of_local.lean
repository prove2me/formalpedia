-- Prove2me | solution 1 for PI.VolStabSW.submDens_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:20:35.168838+00:00
-- url     : https://prove2.me/submissions/43761677-f977-4705-9eb5-2facc8f4157f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfLoc
import Theorems.Thm_PI_VolStabSW_densAll_of_local


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
open MeasureTheory Topology
namespace PI.VolStabSW
theorem _root_.solution (h : SubmLocal) : SubmDens := by
  intro n m μ ν hμ hν f hf
  exact densAll_of_local fun x hx => h n m μ ν hμ hν f hf x hx
end PI.VolStabSW
