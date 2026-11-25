-- Prove2me | solution 1 for P2M_Formalism_YangianSpanCharacter_P_y1__mod_9fb34041d8dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:10:11.378035+00:00
-- url     : https://prove2.me/submissions/9df2991f-bdda-4c56-a53f-f4c76259d8a0

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
import Theorems.Thm_P2M_Formalism_YangianSpanCharacter_P_y1__alg_62a8488f9a3e

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
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {t : 𝕜 → Matrix (Fin 2) (Fin 2) A}
  {τinv : 𝕜 → A} {q : 𝕜 → 𝕜} {S : Set 𝕜}
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution (H : ModHyp t τinv q S) {u v : 𝕜} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    t u 1 1 * mf t τinv v - mf t τinv v * t u 1 1 = t u 1 1 * mu t τinv u v := by
  simp only [mf, mu]
  exact y1'_alg (sub_ne_zero.mpr huv) (H.1 u v 1 1 0 1)
    (by rw [neg_sub]; exact H.1 v u 1 1 0 1)
    (H.2.2.2.1 v hv).1 (H.2.2.2.1 v hv).2 (H.2.2.2.1 u hu).1 (H.2.2.2.2.1 u v).eq
end Formalism.YangianSpanCharacter.P
