-- Prove2me | solution 1 for PI.LevelKSplit.W.MeasAll.maximal_compact_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:25:07.391881+00:00
-- url     : https://prove2.me/submissions/f8dadf51-30dd-481f-b1f8-80165fbf17f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasurableSetBorelOfIsClosed
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousAtPlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOfExistSMeasKf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasAll
import Theorems.Thm_PI_LevelKSplit_W_Cont_continuous_at_place
import Theorems.Thm_PI_LevelKSplit_W_Meas_lattice_borel
import Theorems.Thm_PI_LevelKSplit_W_Meas_measKf_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.MeasAll
namespace PI.LevelKSplit.W.MeasAll
theorem _root_.solution : PI.LevelKSplit.W.MeasKfAll :=
  PI.LevelKSplit.W.Meas.measKf_of PI.LevelKSplit.W.Cont.continuous_at_place
    PI.LevelKSplit.W.Meas.lattice_borel
end PI.LevelKSplit.W.MeasAll
