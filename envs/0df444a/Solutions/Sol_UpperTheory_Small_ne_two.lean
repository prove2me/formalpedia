-- Prove2me | solution 1 for UpperTheory.Small.ne_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:27:24.999873+00:00
-- url     : https://prove2.me/submissions/79ca4a9b-60ae-48a8-8651-4e3ef9b8ab79

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_SmallFacts
import Theorems.Thm_UpperTheory_Small_two_mem

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
theorem _root_.solution {l : ℕ} (h : l ∉ H.small) : l ≠ 2 := by
  rintro rfl
  exact h (two_mem H)
end UpperTheory.Small
