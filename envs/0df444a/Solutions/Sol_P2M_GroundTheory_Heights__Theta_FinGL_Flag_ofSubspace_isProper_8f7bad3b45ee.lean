-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FinGL_Flag_ofSubspace_isProper_8f7bad3b45ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:43:13.219089+00:00
-- url     : https://prove2.me/submissions/d5c04d06-2d38-42cd-9430-fbdf61891391

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
theorem _root_.solution {W : Submodule F (Fin n → F)} (h0 : W ≠ ⊥) (h1 : W ≠ ⊤) :
    (Flag.ofSubspace W).IsProper :=
  ⟨1, by simpa [Flag.ofSubspace] using h0, by simpa [Flag.ofSubspace] using h1⟩
end Flag
end GroundTheory.Heights₂.Theta.FinGL
