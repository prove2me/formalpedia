-- Prove2me | solution 1 for PI.wqUnique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:50:23.104048+00:00
-- url     : https://prove2.me/submissions/7023ce39-9f86-49b4-989c-77f63e334607

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeilQuotMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_WqUniqueOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QLiftIsMulLeftInvariant
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_Weight
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QuotMeasUniq
import Theorems.Thm_PI_QuotMeasUniqW_qmuLift
import Theorems.Thm_PI_QuotMeasUniqW_qmuWeight
import Theorems.Thm_PI_QuotMeasUniqW_wqUnique_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI
namespace PI
theorem _root_.solution : PI.WeilQuotMeas.WqUnique :=
  PI.QuotMeasUniqW.wqUnique_of PI.QuotMeasUniqW.qmuWeight PI.QuotMeasUniqW.qmuLift
end PI
