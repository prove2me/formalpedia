-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FinGL_lineFlag_isProper_c56852137958
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:13.231044+00:00
-- url     : https://prove2.me/submissions/00f2943e-80bd-4ede-a926-d2f48cc0305c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FiniteGL_Mirabolic
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FinGL_Flag_ofSubspace_isProper_8f7bad3b45ee

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
theorem _root_.solution (hn : 1 < n) : (lineFlag n F hn).IsProper := by
  refine Flag.ofSubspace_isProper ?_ ?_
  · rw [Ne, Submodule.span_singleton_eq_bot]
    intro h
    simpa using congrFun h ⟨0, by omega⟩
  · intro htop
    have hmem := (Submodule.eq_top_iff'.mp htop) (Pi.single (⟨1, hn⟩ : Fin n) (1 : F))
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have := congrFun ha ⟨1, hn⟩
    simp at this
end GroundTheory.Heights₂.Theta.FinGL
