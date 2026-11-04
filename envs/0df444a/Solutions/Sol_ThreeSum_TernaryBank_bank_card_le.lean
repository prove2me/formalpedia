-- Prove2me | solution 1 for ThreeSum.TernaryBank.bank_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:15:55.933897+00:00
-- url     : https://prove2.me/submissions/afce1fc4-4144-4888-9330-c65eb4bd8592

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
namespace ThreeSum.TernaryBank
theorem _root_.solution (N T : ℕ) : (bank N T).card ≤ 3 ^ N := by
  calc
    (bank N T).card ≤ (univ : Finset (TritWord N)).card := card_le_card (filter_subset _ _)
    _ = 3 ^ N := by simp [TritWord]
end ThreeSum.TernaryBank
