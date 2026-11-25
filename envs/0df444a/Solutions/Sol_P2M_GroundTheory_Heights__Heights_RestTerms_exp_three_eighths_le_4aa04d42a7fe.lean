-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_exp_three_eighths_le_4aa04d42a7fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:12:15.394708+00:00
-- url     : https://prove2.me/submissions/f36778de-06ba-4fa0-90de-0a540e7ec0ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution : Real.exp (3 / 8) ≤ 1.5 := by
  have he := Real.exp_one_lt_d9
  have h8 : Real.exp (3 / 8) ^ 8 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  by_contra hlt
  push Not at hlt
  have h1 : (1.5 : ℝ) ^ 8 < Real.exp (3 / 8) ^ 8 :=
    pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
  have h2 : Real.exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
  rw [h8] at h1
  norm_num at h1 h2
  linarith
end GroundTheory.Heights₂.Heights.RestTerms
