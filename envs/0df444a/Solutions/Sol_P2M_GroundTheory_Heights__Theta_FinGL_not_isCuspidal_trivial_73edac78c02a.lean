-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FinGL_not_isCuspidal_trivial_73edac78c02a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:09:40.274872+00:00
-- url     : https://prove2.me/submissions/b1763d0f-1cbf-4aa7-8eca-bd8d6d763e1e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FiniteGL_Mirabolic
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FinGL_lineFlag_isProper_c56852137958

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
theorem _root_.solution (hn : 1 < n) :
    ¬ IsCuspidal n F (Representation.trivial ℂ (GL (Fin n) F) ℂ) := by
  intro h
  exact one_ne_zero (h (lineFlag n F hn) (lineFlag_isProper hn) 1 (fun g _ ↦ by simp))
end GroundTheory.Heights₂.Theta.FinGL
