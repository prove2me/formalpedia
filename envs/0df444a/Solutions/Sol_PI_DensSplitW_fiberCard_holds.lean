-- Prove2me | solution 1 for PI.DensSplitW.fiberCard_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:27:45.109229+00:00
-- url     : https://prove2.me/submissions/c8ae80ed-c11b-4bc5-87fa-2ebe16dba2ce

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_PhiXFinrankRange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_CardFibreCompl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_FiberCardHolds
import Theorems.Thm_FibreCount_fiber_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.DensSplitW
namespace PI.DensSplitW
theorem _root_.solution : FiberCard := by
  intro K V U _ _ _ _ _ _ _ φ hφ k g
  exact FibreCount.fiber_card φ hφ g
end PI.DensSplitW
