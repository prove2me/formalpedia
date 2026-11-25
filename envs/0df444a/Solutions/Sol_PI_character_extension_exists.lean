-- Prove2me | solution 1 for PI.character_extension_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:28.366579+00:00
-- url     : https://prove2.me/submissions/e9a9a897-e5df-4815-8424-ba74fec7e7d9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharExtend
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterExtension_UnitsComplexExistsZpow
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharExtend
import Theorems.Thm_PI_CharExtendWork_charExtend_main


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
theorem _root_.solution : PI.CharExtend := PI.CharExtendWork.charExtend_main
end PI
