-- Prove2me | solution 1 for PI.JetsPhW.W.log_derivative_integral_jet_integrality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:36:34.764353+00:00
-- url     : https://prove2.me/submissions/93c25e97-23d6-44cd-86e4-5ffae2fb2579

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_TwoUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ExpLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffPowEqZeroOfDegreeLt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ChainSt
import Theorems.Thm_PI_JetsPhW_W_intMv_subst_X
import Theorems.Thm_PI_JetsPhW_W_L0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.W
open PI.JetsPhW
namespace PI.JetsPhW.W
theorem _root_.solution : LogDer := fun _ _ _ i _ _ hv hf hE => L0 i hf hE (intMv_subst_X hv i)
end PI.JetsPhW.W
