-- Prove2me | solution 1 for ThreeSum.TernaryBank.mem_lowerWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:13.613818+00:00
-- url     : https://prove2.me/submissions/57ab4918-04f4-4fa4-86f8-7ed01bebf288

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_bank

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
namespace ThreeSum.TernaryBank
theorem _root_.solution {N : ℕ} {R Q : TritWord N} :
    R ∈ lowerWords Q ↔ Below R Q := by simp [lowerWords]
end ThreeSum.TernaryBank
