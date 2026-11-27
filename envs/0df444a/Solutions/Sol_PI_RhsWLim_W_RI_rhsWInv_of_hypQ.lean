-- Prove2me | solution 1 for PI.RhsWLim.W.RI.rhsWInv_of_hypQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:15:37.692977+00:00
-- url     : https://prove2.me/submissions/a0843cfc-8d05-4108-9400-e663bd39b30c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvOA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvT
import Theorems.Thm_PI_RhsWLim_W_RI_fibTrans
import Theorems.Thm_PI_RhsWLim_W_RI_rhsWInv_of_hyp
import Theorems.Thm_PI_RhsWLim_W_RI_unimodK


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W
namespace PI.RhsWLim.W.RI
theorem _root_.solution (hQ : HypQ) : RhsWInv := rhsWInv_of_hyp hQ unimodK fibTrans
end PI.RhsWLim.W.RI
