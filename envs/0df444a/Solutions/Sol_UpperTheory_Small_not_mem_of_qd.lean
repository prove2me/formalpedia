-- Prove2me | solution 1 for UpperTheory.Small.not_mem_of_qd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:39:34.747721+00:00
-- url     : https://prove2.me/submissions/5c976118-478c-426a-b8b8-1f2e42575e15

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_SmallFacts
import Theorems.Thm_UpperTheory_Small_q_not_mem
import Theorems.Thm_UpperTheory_Small_d_not_mem

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
theorem _root_.solution {l : ℕ} (hl : l = H.q ∨ l = H.d) : l ∉ H.small := by
  rcases hl with rfl | rfl
  · exact q_not_mem H
  · exact d_not_mem H
end UpperTheory.Small
