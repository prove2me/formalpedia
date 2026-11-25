-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_unitary_c1fb52bd7931
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:12:15.525925+00:00
-- url     : https://prove2.me/submissions/89d4e28d-ece3-4e6b-9454-4b419d98889b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_one_91b9f3a7494d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSection_unitary_identity_83c9d18f71ed

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
    (leviSec H B m)ᴴ * H * leviSec H B m = H := by
  have e1 := leviSection_unitary_identity hH hG 1 (by simp)
  rw [leviSec_one, conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at e1
  rw [leviSection_unitary_identity hH hG m hm, ← e1]
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
