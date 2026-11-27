-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FinGL_isCuspidal_one_390ac6dac105
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:09:28.016654+00:00
-- url     : https://prove2.me/submissions/1720d766-b4f8-4d1d-aa44-b5a51613196b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FiniteGL_Mirabolic
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FinGL_Flag_not_isProper_one_fa331fd698d9

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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 1) F) V) : IsCuspidal 1 F ρ :=
  fun 𝓕 h ↦ absurd h 𝓕.not_isProper_one
end GroundTheory.Heights₂.Theta.FinGL
