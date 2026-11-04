-- Prove2me | solution 1 for ThreeSum.TernaryEuler.predecessor_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:03.457349+00:00
-- url     : https://prove2.me/submissions/61be4939-fa78-4899-81de-19943cb73b35

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Theorems.Thm_ThreeSum_TernaryEuler_weight_split
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
namespace ThreeSum.TernaryEuler
theorem _root_.solution {N : ℕ} (R A : TritWord N) (i : Fin N) :
    weight (predecessor R i) A = digitChoose (predDigit (R i)) (A i) *
      ∏ j ∈ (univ : Finset (Fin N)).erase i, digitChoose (R j) (A j) := by
  rw [weight_split _ _ i]
  simp only [predecessor, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [Function.update_of_ne (mem_erase.mp hj).1]
end ThreeSum.TernaryEuler
