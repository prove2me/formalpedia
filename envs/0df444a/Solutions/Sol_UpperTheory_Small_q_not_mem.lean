-- Prove2me | solution 1 for UpperTheory.Small.q_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:25:32.899727+00:00
-- url     : https://prove2.me/submissions/a8d006b4-1602-43b9-9073-392b3872b532

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
theorem _root_.solution : H.q ∉ H.small := not_mem_of_dvd_qd H (dvd_mul_right _ _)
end UpperTheory.Small
