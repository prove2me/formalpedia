-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSection_unitary_identity_83c9d18f71ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:28:29.972415+00:00
-- url     : https://prove2.me/submissions/a7cc9b69-e783-4381-8418-24f4c96ec131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_gram_mul_leftInv_d1f3a43f7061

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
open Matrix
noncomputable section
set_option linter.unusedSectionVars false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {H : Matrix ι ι ℂ} {B : Matrix ι κ ℂ}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
theorem _root_.solution (hH : Hᴴ = H) (hG : IsUnit (Bᴴ * H * B).det) (m : Matrix κ κ ℂ)
    (hm : mᴴ * (Bᴴ * H * B) * m = Bᴴ * H * B) :
    (leviSec H B m)ᴴ * H * leviSec H B m =
      (1 - B * leftInv H B)ᴴ * (H * (1 - B * leftInv H B)) +
        (leftInv H B)ᴴ * (Bᴴ * (H * (B * leftInv H B))) := by
  have K : Bᴴ * (H * (1 - B * leftInv H B)) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc H, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, gram_mul_leftInv hG, sub_self]
  have K' : ∀ N : Matrix κ ι ℂ, (1 - B * leftInv H B)ᴴ * (H * (B * N)) = 0 := by
    intro N
    have := congrArg conjTranspose K
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH, conjTranspose_zero]
      at this
    rw [← Matrix.mul_assoc H, ← Matrix.mul_assoc, ← Matrix.mul_assoc, this, Matrix.zero_mul]
  have hmx : ∀ N : Matrix κ ι ℂ, mᴴ * (Bᴴ * (H * (B * (m * N)))) = Bᴴ * (H * (B * N)) := by
    intro N
    have := congrArg (· * N) hm
    simp only [Matrix.mul_assoc] at this
    exact this
  unfold leviSec
  rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, K, K', hmx, Matrix.mul_zero,
    add_zero, zero_add]
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
