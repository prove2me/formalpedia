-- Prove2me | solution 1 for ThreeSum.TernaryBank.rank_add_deficit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:35:17.561829+00:00
-- url     : https://prove2.me/submissions/a95a8e3c-f7ab-4ae9-b490-69d70046f1ce

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
namespace ThreeSum.TernaryBank
theorem _root_.solution {N : ℕ} {R Q : TritWord N} (h : Below R Q) :
    rank R + deficit Q R = rank Q := by
  unfold rank deficit
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact Nat.add_sub_of_le (h i)
end ThreeSum.TernaryBank
