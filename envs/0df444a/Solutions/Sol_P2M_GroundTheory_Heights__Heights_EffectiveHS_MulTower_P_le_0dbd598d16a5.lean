-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_P_le_0dbd598d16a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:05.606817+00:00
-- url     : https://prove2.me/submissions/192e4409-fee8-4ebe-b2e0-3161dfec7e96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_mono_9328e92a5316

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (τ : MulTower R A)
variable {D : ℕ} {s : Fin D → A}
namespace GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
theorem _root_.solution (hs : ∀ i, s i ∈ τ.W) {T : ℕ} (hDT : D ≤ T) : τ.P D T s ≤ τ.V T := by
  rw [P, Submodule.span_le]
  rintro F ⟨α, h, hh, hα, rfl⟩
  have h' := τ.raises_mono hs α D h hh
  rwa [hα, Nat.add_sub_cancel' hDT] at h'
end GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
