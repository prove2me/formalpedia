-- Prove2me | solution 1 for PI.BeConjNormW.beConjNorm_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:38.468011+00:00
-- url     : https://prove2.me/submissions/b6eb1649-c95f-4539-8589-86d2debf72ae

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BeConjNorm
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsOfCalculation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeConjNormW
open PI.PhNormUnits
namespace PI.BeConjNormW
theorem _root_.solution (h : StepCore) : PI.BeConjNorm.BeConjNorm := h
end PI.BeConjNormW
