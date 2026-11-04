-- Prove2me | solution 1 for ThreeSum.TernaryBank.deficit_generating_sum_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:05.784428+00:00
-- url     : https://prove2.me/submissions/395bd830-a1e8-4d36-9ea4-d1b2b2d44a57

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Theorems.Thm_ThreeSum_TernaryBank_deficit_generating_sum
import Theorems.Thm_ThreeSum_TernaryBank_deficit_product_eq_counts

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
namespace ThreeSum.TernaryBank
theorem _root_.solution {N : ℕ} (Q : TritWord N) (z : ℝ) :
    (∑ R ∈ lowerWords Q, z ^ deficit Q R) =
    (1 + z) ^ digitCount Q 1 * (1 + z + z ^ 2) ^ digitCount Q 2 := by
  rw [deficit_generating_sum, deficit_product_eq_counts]
end ThreeSum.TernaryBank
