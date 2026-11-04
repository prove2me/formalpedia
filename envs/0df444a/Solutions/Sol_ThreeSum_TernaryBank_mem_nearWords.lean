-- Prove2me | solution 1 for ThreeSum.TernaryBank.mem_nearWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:01:32.440516+00:00
-- url     : https://prove2.me/submissions/eb849454-8585-4b05-baf3-3d60a0889382

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
namespace ThreeSum.TernaryBank
theorem _root_.solution {N D : ℕ} {R Q : TritWord N} :
    R ∈ nearWords Q D ↔ Below R Q ∧ deficit Q R ≤ D := by simp [nearWords]
end ThreeSum.TernaryBank
