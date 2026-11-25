-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_proof_430964d65828
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:04:37.378608+00:00
-- url     : https://prove2.me/submissions/6a23df3a-f7ca-43b4-9a9a-91d0e794df3f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbAddBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_finrank_gradedPiece_348cd7d65ded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace HilbAddBlock
theorem _root_.solution : HilbAddBlock.Statement := by
  intro F _ K _ _ ι _ I N m
  unfold hilbFn projSpaceHilb
  by_cases h : ∀ o, 0 ≤ m o
  · rw [if_pos h, if_pos (fun k => h (some k)), if_pos (h none),
      HilbAddBlock.finrank_gradedPiece]
    push_cast
    rfl
  · rw [if_neg h]
    push Not at h
    obtain ⟨o, ho⟩ := h
    cases o with
    | none => rw [if_neg (not_le.mpr ho), mul_zero]
    | some k => rw [if_neg (fun h' => absurd (h' k) (not_le.mpr ho)), zero_mul]
end HilbAddBlock
end GroundTheory.Heights₂.Heights.FieldNumbers
