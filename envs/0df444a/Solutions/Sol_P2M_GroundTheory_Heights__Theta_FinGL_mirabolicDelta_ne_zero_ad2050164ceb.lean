-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FinGL_mirabolicDelta_ne_zero_ad2050164ceb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:09:36.457284+00:00
-- url     : https://prove2.me/submissions/ac9b0d0d-9d56-4137-94ce-891cc1403945

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
variable [NeZero n]
namespace GroundTheory.Heights₂.Theta.FinGL
theorem _root_.solution (ψ₀ : AddChar F ℂ) : mirabolicDelta n F ψ₀ ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : MirabolicInducedSpace n F ψ₀ ↦ (f : mirabolic n F → ℂ) 1) h
  have hone : ((1 : mirabolic n F) : GL (Fin n) F) ∈ upperUnipotent n F := one_mem _
  simp only [mirabolicDelta, mirabolicDeltaFun, dif_pos hone] at h1
  rw [show (⟨((1 : mirabolic n F) : GL (Fin n) F), hone⟩ : upperUnipotent n F) = 1 from rfl,
    map_one] at h1
  exact one_ne_zero h1
end GroundTheory.Heights₂.Theta.FinGL
