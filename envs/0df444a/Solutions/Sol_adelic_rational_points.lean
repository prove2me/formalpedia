-- Prove2me | solution 1 for adelic_rational_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:00:10.069804+00:00
-- url     : https://prove2.me/submissions/997eb114-c71d-43d7-9e99-d33dda11947b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalPointsComparison_BridgeApplyEqOfComp
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_BridgeRatPts
import Theorems.Thm_Formalism_L2_SG_AdBridge_adBridgeGF_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeGF I :=
  Formalism.L2.SG.AdBridge.adBridgeGF_main
