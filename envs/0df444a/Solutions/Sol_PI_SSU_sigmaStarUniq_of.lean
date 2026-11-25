-- Prove2me | solution 1 for PI.SSU.sigmaStarUniq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:16.91086+00:00
-- url     : https://prove2.me/submissions/0d7f9b8a-38cd-4719-8de8-f6e1471f2ec7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_CoefShift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_ZeroOfCoef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_SiegelSetShiftInvariance
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_SiegelSetCompleteness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_SigmaStarUniqOf
import Theorems.Thm_PI_SSU_key_of
import Theorems.Thm_PI_SSU_main_of
import Theorems.Thm_PI_SSU_siegel_set_completeness
import Theorems.Thm_PI_SSU_siegel_set_shift_invariance


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.SSU
namespace PI.SSU
theorem _root_.solution (h : AreaLat) : SigmaStarUniq :=
  main_of (key_of siegel_set_shift_invariance siegel_set_completeness) h
end PI.SSU
