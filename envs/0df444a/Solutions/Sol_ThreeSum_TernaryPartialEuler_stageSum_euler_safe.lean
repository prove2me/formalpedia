-- Prove2me | solution 1 for ThreeSum.TernaryPartialEuler.stageSum_euler_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:43:43.463892+00:00
-- url     : https://prove2.me/submissions/30080f56-9298-480a-99d7-0a284bdfbed1

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Theorems.Thm_ThreeSum_TernaryPartialEuler_stageSum_euler
import Theorems.Thm_ThreeSum_TernaryPartialEuler_safe_sum_eq

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartialEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryPartialEuler
theorem _root_.solution {N h : ℕ} (S : Finset (Fin N)) (f : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=h) (R dummy : TritWord N) :
    (∑ i : Fin N, restrictedWeight S R i*
        stageSum S f (safePredecessor S R dummy i))=
      ((rank R : ℤ)-(h : ℤ))*stageSum S f R := by
  rw [safe_sum_eq]
  exact stageSum_euler S f hf R
end ThreeSum.TernaryPartialEuler
