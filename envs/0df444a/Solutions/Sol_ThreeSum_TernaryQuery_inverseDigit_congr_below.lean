-- Prove2me | solution 1 for ThreeSum.TernaryQuery.inverseDigit_congr_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:00.701438+00:00
-- url     : https://prove2.me/submissions/7fe6e623-acb1-473b-aea8-4cf5cb0ed662

import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryQuery
open ThreeSum.TernaryJointType
open ThreeSum.TernaryBank
namespace ThreeSum.TernaryQuery
theorem _root_.solution (f g : Fin 3 → ℤ) (d : Fin 3)
    (h : ∀ e ≤ d, f e = g e) : inverseDigit f d = inverseDigit g d := by
  fin_cases d
  · simp [inverseDigit, h 0 (by decide)]
  · simp [inverseDigit, h 0 (by decide), h 1 (by decide)]
  · simp [inverseDigit, h 0 (by decide), h 1 (by decide), h 2 (by decide)]
end ThreeSum.TernaryQuery
