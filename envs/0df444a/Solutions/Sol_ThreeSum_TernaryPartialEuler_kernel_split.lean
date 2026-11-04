-- Prove2me | solution 1 for ThreeSum.TernaryPartialEuler.kernel_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:58.966098+00:00
-- url     : https://prove2.me/submissions/cf2efbe1-8139-457f-81b9-98322fa95a6e

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
    (i : Fin N) (hi : i∈S) :
    kernel S R A=digitChoose (R i) (A i)*
      ∏ j∈(univ : Finset (Fin N)).erase i,
        if j∈S then digitChoose (R j) (A j) else if A j=R j then 1 else 0 := by
  unfold kernel
  rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
  simp [hi]
end ThreeSum.TernaryPartialEuler
