-- Prove2me | solution 1 for ThreeSum.TernaryDimensionBounds.bank_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:45.357281+00:00
-- url     : https://prove2.me/submissions/2b514609-1099-47be-8563-7ac278f8491e

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
import Theorems.Thm_ThreeSum_TernaryDimensionBounds_bank_pos
import Theorems.Thm_ThreeSum_TernaryBank_bank_card_gibbs
import Theorems.Thm_ThreeSum_TernaryParameters_generating_polynomials
import Theorems.Thm_ThreeSum_TernaryParameters_gibbs_parameters


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryDimensionBounds
open TernaryJointType TernaryLocalParameters TernaryBank TernaryParameters
namespace ThreeSum.TernaryDimensionBounds
theorem _root_.solution (m j : ℕ) :
    Real.log (bankSize m j : ℝ) ≤ (fixedLength (j*m) : ℝ)*Real.log 2*bankEntropy := by
  have hy := gibbs_parameters
  have hc : 0 < (bankSize m j : ℝ) := by exact_mod_cast bank_pos (fixedLength (j*m)) (bankCut m j)
  have hg := bank_card_gibbs (fixedLength (j*m)) (bankCut m j) y hy.1.le hy.2.1.le
  have hh := Real.log_le_log (mul_pos hc (pow_pos hy.1 _)) hg
  rw [Real.log_mul hc.ne' (pow_pos hy.1 _).ne', Real.log_pow, Real.log_pow,
    ← generating_polynomials.1] at hh
  change Real.log (bankSize m j : ℝ)+(bankCut m j : ℝ)*Real.log y ≤
    (fixedLength (j*m) : ℝ)*Real.log bankArg at hh
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*bankEntropy =
      (fixedLength (j*m) : ℝ)*Real.log bankArg-(bankCut m j : ℝ)*Real.log y := by
    unfold bankEntropy mean pi1 pi2 TernaryParameters.deficit bankCut fixedLength
    push_cast
    field_simp
    ring
  rw [he]
  linarith
end ThreeSum.TernaryDimensionBounds
