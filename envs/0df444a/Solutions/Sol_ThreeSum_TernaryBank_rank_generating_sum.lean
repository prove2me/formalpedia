-- Prove2me | solution 1 for ThreeSum.TernaryBank.rank_generating_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:03:49.922201+00:00
-- url     : https://prove2.me/submissions/5c714571-a7bf-4e14-9edb-cdf2e6c126b6

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
theorem _root_.solution (N : ℕ) (y : ℝ) :
    (∑ R : TritWord N, y ^ rank R) = (1 + y + y ^ 2) ^ N := by
  have h := Fintype.sum_pow (fun d : Fin 3 => y ^ d.val) N
  have hlocal : (∑ d : Fin 3, y ^ d.val) = 1 + y + y ^ 2 := by
    simp [Fin.sum_univ_succ]
    ring
  rw [hlocal] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro R hR
  exact (Finset.prod_pow_eq_pow_sum univ (fun i => (R i).val) y).symm
end ThreeSum.TernaryBank
