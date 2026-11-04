-- Prove2me | solution 1 for ThreeSum.TernaryDimensionBounds.query_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:46.549581+00:00
-- url     : https://prove2.me/submissions/48806eb1-aa41-4c45-b353-9b85f175a0a6

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
import Theorems.Thm_ThreeSum_TernaryDimensionBounds_near_pos
import Theorems.Thm_ThreeSum_TernaryBank_nearWords_card_gibbs_counts
import Theorems.Thm_ThreeSum_TernaryParameters_generating_polynomials
import Theorems.Thm_ThreeSum_TernaryParameters_gibbs_parameters


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryDimensionBounds
open TernaryJointType TernaryLocalParameters TernaryBank TernaryParameters
namespace ThreeSum.TernaryDimensionBounds
theorem _root_.solution {m j : ℕ} (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    Real.log ((nearWords Q (queryDeficit m j)).card : ℝ) ≤
      (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy-Real.log z := by
  have hz := gibbs_parameters
  have hc : 0 < ((nearWords Q (queryDeficit m j)).card : ℝ) := by exact_mod_cast near_pos Q _
  have hg := nearWords_card_gibbs_counts Q (queryDeficit m j) z hz.2.2.1.le hz.2.2.2.le
  rw [hQ 1,hQ 2] at hg
  have hh := Real.log_le_log (mul_pos hc (pow_pos hz.2.2.1 _)) hg
  have ha1 : 0 < 1+z := by linarith [hz.2.2.1]
  have ha2 : 0 < 1+z+z^2 := by nlinarith [sq_nonneg z]
  rw [Real.log_mul hc.ne' (pow_pos hz.2.2.1 _).ne', Real.log_pow,
    Real.log_mul (pow_pos ha1 _).ne' (pow_pos ha2 _).ne',Real.log_pow,Real.log_pow,
    ← generating_polynomials.2.2,← generating_polynomials.2.1] at hh
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy-Real.log z =
      (fixedPi (j*m) 1 : ℝ)*Real.log queryArg1+(fixedPi (j*m) 2 : ℝ)*Real.log queryArg2-
        (queryDeficit m j : ℝ)*Real.log z := by
    unfold queryEntropy pi1 pi2 TernaryParameters.deficit queryDeficit fixedLength fixedPi
    norm_num
    push_cast
    field_simp
    ring
  rw [he]
  linarith
end ThreeSum.TernaryDimensionBounds
