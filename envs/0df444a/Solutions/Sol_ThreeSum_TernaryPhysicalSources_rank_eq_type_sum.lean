-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalSources.rank_eq_type_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:41.249682+00:00
-- url     : https://prove2.me/submissions/e6b81f8f-bfed-4c33-ab6d-bb9149c774fd

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPhysicalSources
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryConvolution
namespace ThreeSum.TernaryPhysicalSources
theorem _root_.solution {N : ℕ} (R : TritWord N) :
    rank R = ∑ d : Fin 3, d.val*digitCount R d := by
  unfold rank digitCount
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hs : ∀ r : Fin 3, r.val = ∑ d : Fin 3,
      d.val*(if r=d then 1 else 0 : ℕ) := by
    intro r
    fin_cases r <;> decide
  exact hs (R i)
end ThreeSum.TernaryPhysicalSources
