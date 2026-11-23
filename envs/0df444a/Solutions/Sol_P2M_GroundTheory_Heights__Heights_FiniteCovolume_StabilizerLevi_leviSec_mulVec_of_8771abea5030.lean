-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_mulVec_of_8771abea5030
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:41.692295+00:00
-- url     : https://prove2.me/submissions/890e415c-7c58-4ba0-9957-d04ba7a90754

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mulVec_eq_zero_a4db1ca55c07

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
theorem _root_.solution {X : ι → ℂ} (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0) (m : Matrix κ κ ℂ) :
    leviSec H B m *ᵥ X = X := by
  have hAX := leftInv_mulVec_eq_zero hBX
  simp only [leviSec, add_mulVec, sub_mulVec, Matrix.one_mulVec, ← mulVec_mulVec, hAX, mulVec_zero,
    sub_zero, add_zero]
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
