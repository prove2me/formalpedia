-- Prove2me | solution 1 for bilinearDensityFormula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:57.239701+00:00
-- url     : https://prove2.me/submissions/b02fd654-0fac-4dda-8f9c-f90ce350d141

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_FiberCardHolds
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DensSplit
import Theorems.Thm_PI_DensSplitW_densExactSplit_of
import Theorems.Thm_PI_DensSplitW_fiberCard_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.L2.SG.DensExact.DensExactSplit :=
  PI.DensSplitW.densExactSplit_of PI.DensSplitW.fiberCard_holds
