-- Prove2me | solution 1 for ThreeSum.TernaryPartialEuler.safe_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:24:01.35784+00:00
-- url     : https://prove2.me/submissions/dd60acc3-bb44-4909-bc6e-0203abb44c67

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
theorem _root_.solution {N : ℕ} (S : Finset (Fin N)) (R dummy : TritWord N)
    (F : TritWord N→ℤ) :
    (∑ i : Fin N, restrictedWeight S R i*F (safePredecessor S R dummy i))=
      ∑ i∈S, (R i).val*F (predecessor R i) := by
  have he : (∑ i : Fin N, restrictedWeight S R i*F (safePredecessor S R dummy i))=
      ∑ i : Fin N, if i∈S then (R i).val*F (predecessor R i) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hs : i∈S
    · by_cases hz : (R i).val=0
      · simp [restrictedWeight,safePredecessor,hs,hz]
      · have hp : 0<(R i).val := Nat.pos_of_ne_zero hz
        simp [restrictedWeight,safePredecessor,hs,hp]
    · simp [restrictedWeight,hs]
  rw [he,←Finset.sum_filter]
  simp
end ThreeSum.TernaryPartialEuler
