-- Prove2me | solution 1 for UpperTheory.Small.d_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:49:37.128788+00:00
-- url     : https://prove2.me/submissions/09327ef2-c84f-4d1c-8a37-ac7917c45510

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_SmallFacts
import Theorems.Thm_UpperTheory_Small_not_mem_of_dvd_qd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Small
open Formalism.BasicNotions
variable {R : Ranks} (H : Host R)
namespace UpperTheory.Small
theorem _root_.solution : H.d ∉ H.small := not_mem_of_dvd_qd H (dvd_mul_left _ _)
end UpperTheory.Small
