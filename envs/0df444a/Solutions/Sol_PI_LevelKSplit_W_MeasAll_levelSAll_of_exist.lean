-- Prove2me | solution 1 for PI.LevelKSplit.W.MeasAll.levelSAll_of_exist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:27.773107+00:00
-- url     : https://prove2.me/submissions/78fd8dd0-e2ff-4584-923a-f35a6e58ac03

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasurableSetBorelOfIsClosed
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousAtPlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOfExistSMeasKf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasAll
import Theorems.Thm_PI_LevelKSplit_W_MeasAll_maximal_compact_measurable
import Theorems.Thm_PI_LevelKSplit_W_Split_levelSAll_of_existS_measKf


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
theorem _root_.solution (h1 : PI.LevelKSplit.W.ExistSAll) : PI.LevelKSplit.LevelSAll :=
  PI.LevelKSplit.W.Split.levelSAll_of_existS_measKf h1 maximal_compact_measurable
end PI.LevelKSplit.W.MeasAll
