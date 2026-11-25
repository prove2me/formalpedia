-- Prove2me | solution 1 for P2M_Formalism_YangianSpanCharacter_P_from_comm__4b04a0b711b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:49:06.090526+00:00
-- url     : https://prove2.me/submissions/47b02d6f-2dd5-4d3e-9049-2dadb47ab50f

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution {b m e : A} (h : b * m - m * b = b * e) : m * b = b * (m - e) := by
  rw [mul_sub]
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel
end Formalism.YangianSpanCharacter.P
