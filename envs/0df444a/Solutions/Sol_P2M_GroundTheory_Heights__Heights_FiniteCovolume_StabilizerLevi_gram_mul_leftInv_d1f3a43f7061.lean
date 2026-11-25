-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_gram_mul_leftInv_d1f3a43f7061
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:16.497151+00:00
-- url     : https://prove2.me/submissions/cc41a57d-afd1-44d0-9dcf-8e65f0cdcb58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices

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
theorem _root_.solution (hG : IsUnit (Bᴴ * H * B).det) :
    Bᴴ * H * B * leftInv H B = Bᴴ * H := by
  unfold leftInv
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hG, Matrix.one_mul]
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
