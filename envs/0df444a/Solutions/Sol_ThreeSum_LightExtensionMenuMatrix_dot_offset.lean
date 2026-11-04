-- Prove2me | solution 1 for ThreeSum.LightExtensionMenuMatrix.dot_offset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:39.155307+00:00
-- url     : https://prove2.me/submissions/4d60f8ea-3905-44db-9b79-169e57a3bb63

import Definitions.Def_Submission_ThreeSum_LightExtensionFieldMultiply
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuSemantics
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_involutive
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_lt


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionMenuMatrix
open TernaryExtensionEncoding
set_option maxHeartbeats 2000000
variable {p : ℕ} [Fact p.Prime] {f : Polynomial (ZMod p)}
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
namespace ThreeSum.LightExtensionMenuMatrix
theorem _root_.solution (J : ℕ) (f g : ℕ → ℕ) :
    LightNaturalDot.dot (fun i => f (TernarySignedLayout.offset J i))
      (fun i => g (TernarySignedLayout.offset J i)) (J+2)=LightNaturalDot.dot f g (J+2) := by
  unfold LightNaturalDot.dot LightBooleanDot.dot
  apply Finset.sum_bij (fun i _ => TernarySignedLayout.offset J i)
  · intro i hi
    exact Finset.mem_range.mpr (TernarySignedLayout.offset_lt (Finset.mem_range.mp hi))
  · intro i hi j hj hij
    have h := congrArg (TernarySignedLayout.offset J) hij
    rwa [TernarySignedLayout.offset_involutive (Finset.mem_range.mp hi),
      TernarySignedLayout.offset_involutive (Finset.mem_range.mp hj)] at h
  · intro j hj
    refine ⟨TernarySignedLayout.offset J j,
      Finset.mem_range.mpr (TernarySignedLayout.offset_lt (Finset.mem_range.mp hj)),?_⟩
    exact TernarySignedLayout.offset_involutive (Finset.mem_range.mp hj)
  · intro i hi
    rfl
end ThreeSum.LightExtensionMenuMatrix
