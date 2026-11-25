-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesGenIndexMono_proof_2040980b39c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:50.825164+00:00
-- url     : https://prove2.me/submissions/20e5430b-c591-4f39-9e43-2c944f2f096a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexMono
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGenIndexMono_genIndex_of_le_e2c91bfa825c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGenIndexMono_genIndex_nonneg_9f837cd075ce

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
open KLinesGenIndexMono
namespace GroundTheory.Heights₂.Heights
namespace LinesGenIndexMono
theorem _root_.solution (h1 : LinesGenIndexTrans.Statement) : LinesGenIndexMono.Statement := by
  intro V _ _ _ A A' B hA hA' hB hle
  obtain ⟨hpos, heq⟩ := h1 V A' A B hA' hA hB
  have hle' : A.toAddSubgroup ≤ A'.toAddSubgroup := hle
  rw [← heq]
  rw [genIndex_of_le hle'] at hpos ⊢
  have hone : (1 : ℝ) ≤ (A.toAddSubgroup.relIndex A'.toAddSubgroup : ℝ) := by
    have : 0 < A.toAddSubgroup.relIndex A'.toAddSubgroup := by exact_mod_cast hpos
    exact_mod_cast this
  exact le_mul_of_one_le_left (genIndex_nonneg _ _) hone
end LinesGenIndexMono
end GroundTheory.Heights₂.Heights
