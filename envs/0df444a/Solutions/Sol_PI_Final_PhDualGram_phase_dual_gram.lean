-- Prove2me | solution 1 for PI.Final.PhDualGram.phase_dual_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:10:46.964172+00:00
-- url     : https://prove2.me/submissions/ac82e859-3e90-4442-a57f-e22634bab41d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_PhDualGramMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PhDualGram
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_phDualGram_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Final PI.Final.PhDualGram
namespace PI.Final.PhDualGram
theorem _root_.solution : PI.FglGram.PhDualGram := PI.UnitaryGroupMassFormula.PhDualGram.phDualGram_main
end PI.Final.PhDualGram
