-- Prove2me | solution 1 for ThreeSum.TernaryReconstruction.firstCross_eq_frozenInverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:05.917236+00:00
-- url     : https://prove2.me/submissions/1b85017c-e5e3-401a-916f-3065e06d4bab

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryReconstruction
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryQuery ThreeSum.TernaryEuler
namespace ThreeSum.TernaryReconstruction
theorem _root_.solution {N : ℕ} (T : ℕ) (H : TritWord N → ℤ)
    (coords : List (Fin N)) (R : TritWord N) :
    firstCross T H coords R = frozenInverse coords H R := by
  induction coords generalizing R with
  | nil => rfl
  | cons i rest ih =>
      simp only [firstCross]
      split_ifs with h
      · rfl
      · simp only [frozenInverse, ih]
end ThreeSum.TernaryReconstruction
