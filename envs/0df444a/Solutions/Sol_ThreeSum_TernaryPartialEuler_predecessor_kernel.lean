-- Prove2me | solution 1 for ThreeSum.TernaryPartialEuler.predecessor_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:58.552531+00:00
-- url     : https://prove2.me/submissions/95357600-254a-48f8-a8da-539f08b6a69a

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Theorems.Thm_ThreeSum_TernaryPartialEuler_kernel_split
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
    kernel S (predecessor R i) A=digitChoose (predDigit (R i)) (A i)*
      ∏ j∈(univ : Finset (Fin N)).erase i,
        if j∈S then digitChoose (R j) (A j) else if A j=R j then 1 else 0 := by
  rw [kernel_split S _ A i hi]
  simp only [predecessor,Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [Function.update_of_ne (mem_erase.mp hj).1]
end ThreeSum.TernaryPartialEuler
