-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_mul_B_0f87ab092af1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:54:17.000662+00:00
-- url     : https://prove2.me/submissions/1bcaf52f-c943-4039-8890-f6c4b5ea2bbf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mul_24167f725f84

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
theorem _root_.solution (hG : IsUnit (Bᴴ * H * B).det) (m : Matrix κ κ ℂ) :
    leviSec H B m * B = B * m := by
  have h2 := leftInv_mul hG (H := H) (B := B)
  unfold leviSec
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  abel
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
