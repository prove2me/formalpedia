-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_Vpp_le_ae2dcd98d56b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:55:48.161856+00:00
-- url     : https://prove2.me/submissions/e2490fcd-fe1f-48b4-970e-18bc33694d35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_gen_mem_300a56edc436
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_P_le_0dbd598d16a5

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
theorem _root_.solution (hs : ∀ i, s i ∈ τ.W) {T a₀ : ℕ} (hDT : D ≤ T) : τ.Vpp D T a₀ s ≤ τ.V T := by
  refine sup_le ?_ (τ.P_le hs hDT)
  rw [Submodule.span_le]
  rintro F ⟨α, k, w, m, hw, hm, hT, -, rfl⟩
  exact τ.gen_mem hs α w hw hm hT
end GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
