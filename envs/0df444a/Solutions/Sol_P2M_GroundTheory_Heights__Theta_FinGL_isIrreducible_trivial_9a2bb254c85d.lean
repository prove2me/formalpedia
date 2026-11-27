-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FinGL_isIrreducible_trivial_9a2bb254c85d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:09:32.851002+00:00
-- url     : https://prove2.me/submissions/a5d6c627-e1f3-4737-9cbf-b77c99111351

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
theorem _root_.solution (G : Type*) [Group G] :
    (Representation.trivial ℂ G ℂ).IsIrreducible := by
  have hbt : ((⊥ : Subrepresentation (Representation.trivial ℂ G ℂ)).toSubmodule) ≠
      (⊤ : Subrepresentation (Representation.trivial ℂ G ℂ)).toSubmodule :=
    bot_ne_top (α := Submodule ℂ ℂ)
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun h ↦ hbt (congrArg _ h)⟩⟩, eq_bot_or_eq_top := fun σ ↦ ?_ }
  rcases IsSimpleOrder.eq_bot_or_eq_top σ.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)
end GroundTheory.Heights₂.Theta.FinGL
