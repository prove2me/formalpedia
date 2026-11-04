-- Prove2me | solution 1 for ThreeSum.TernaryPartialEuler.outside_difference_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:24:00.014945+00:00
-- url     : https://prove2.me/submissions/18574112-b65d-451c-b5d0-8ca3a071a77c

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartialEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryPartialEuler
theorem _root_.solution {N : ℕ} (S : Finset (Fin N)) (R A : TritWord N)
    (i : Fin N) (hi : i∉S) :
    ((R i).val-(A i).val : ℤ)*kernel S R A=0 := by
  by_cases he : A i=R i
  · simp [he]
  · have hz : kernel S R A=0 := by
      unfold kernel
      exact Finset.prod_eq_zero (mem_univ i) (by simp [hi,he])
    simp [hz]
end ThreeSum.TernaryPartialEuler
