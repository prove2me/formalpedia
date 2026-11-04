-- Prove2me | solution 1 for ThreeSum.TernaryConvolution.frozenInverse_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:44.328936+00:00
-- url     : https://prove2.me/submissions/0c6c61ec-7446-444d-a578-d1f1e43e8762

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryConvolution
theorem _root_.solution {N : ℕ} (xs ys : List (Fin N)) (H : TritWord N → ℤ) :
    frozenInverse (xs++ys) H=frozenInverse xs (frozenInverse ys H) := by
  induction xs with
  | nil => rfl
  | cons i rest ih =>
    funext Q
    simp only [List.cons_append,frozenInverse,ih]
end ThreeSum.TernaryConvolution
