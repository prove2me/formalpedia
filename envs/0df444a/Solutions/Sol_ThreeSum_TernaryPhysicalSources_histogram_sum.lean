-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalSources.histogram_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:45.013118+00:00
-- url     : https://prove2.me/submissions/902c3926-68ad-4bf9-ac65-1bec09e25aa1

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
variable {ι κ : Type*}
namespace ThreeSum.TernaryPhysicalSources
theorem _root_.solution {N : ℕ} (S : Finset ι) (word : ι → TritWord N)
    (F : TritWord N → ℤ) :
    (∑ A, histogram S word A*F A) = ∑ i ∈ S, F (word i) := by
  classical
  unfold histogram
  simp only [Finset.sum_mul,ite_mul,one_mul,zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp
end ThreeSum.TernaryPhysicalSources
