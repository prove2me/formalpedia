-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FinGL_Flag_not_isProper_one_fa331fd698d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:43:09.927804+00:00
-- url     : https://prove2.me/submissions/0c9d5af6-4272-447c-816a-de0600a9a500

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FiniteGL_Mirabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FinGL
open Matrix
noncomputable section
variable {n : ℕ} {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Theta.FinGL
namespace Flag
theorem _root_.solution (𝓕 : Flag 1 F) : ¬ 𝓕.IsProper := by
  rintro ⟨i, h0, h1⟩
  haveI : IsSimpleModule F (Fin 1 → F) := isSimpleModule_iff_finrank_eq_one.mpr (by simp)
  rcases IsSimpleOrder.eq_bot_or_eq_top (𝓕.space i) with h | h
  · exact h0 h
  · exact h1 h
end Flag
end GroundTheory.Heights₂.Theta.FinGL
