-- Prove2me | solution 1 for ThreeSum.TernaryPartialEuler.kernel_euler
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:40:36.31456+00:00
-- url     : https://prove2.me/submissions/5233f40a-a467-448f-bc61-4ba1e6944467

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Theorems.Thm_ThreeSum_TernaryPartialEuler_coordinate_kernel_euler
import Theorems.Thm_ThreeSum_TernaryPartialEuler_outside_difference_zero
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
theorem _root_.solution {N : ℕ} (S : Finset (Fin N)) (R A : TritWord N) :
    (∑ i∈S, (R i).val*kernel S (predecessor R i) A)=
      ((rank R : ℤ)-(rank A : ℤ))*kernel S R A := by
  calc
    (∑ i∈S, (R i).val*kernel S (predecessor R i) A) =
        ∑ i∈S, ((R i).val-(A i).val : ℤ)*kernel S R A := by
      apply Finset.sum_congr rfl
      intro i hi
      exact coordinate_kernel_euler S R A i hi
    _ = ∑ i : Fin N, ((R i).val-(A i).val : ℤ)*kernel S R A := by
      apply Finset.sum_subset (subset_univ S)
      intro i hi hnot
      exact outside_difference_zero S R A i hnot
    _ = ((rank R : ℤ)-(rank A : ℤ))*kernel S R A := by
      rw [←Finset.sum_mul,Finset.sum_sub_distrib]
      simp [rank]
end ThreeSum.TernaryPartialEuler
