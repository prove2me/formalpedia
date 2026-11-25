-- Prove2me | solution 1 for cCRuleC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:02:39.678903+00:00
-- url     : https://prove2.me/submissions/ea941b16-8e88-4f1e-8ea8-2132d1672a40

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CCRuleC
import Theorems.Thm_CCRuleCW_ruleC


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.C2.RuleC := CCRuleCW.ruleC
