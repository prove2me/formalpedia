-- Prove2me | solution 1 for ThreeSum.TernaryEuler.weight_euler
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:08:24.064268+00:00
-- url     : https://prove2.me/submissions/0eb806e6-41b6-42f0-ab4d-42fda024b820

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Theorems.Thm_ThreeSum_TernaryEuler_coordinate_weight_euler
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
theorem _root_.solution {N : ℕ} (R A : TritWord N) :
    (∑ i : Fin N, (R i).val * weight (predecessor R i) A) =
      ((rank R : ℤ) - (rank A : ℤ)) * weight R A := by
  simp only [coordinate_weight_euler, ← Finset.sum_mul, Finset.sum_sub_distrib]
  simp [rank]
end ThreeSum.TernaryEuler
