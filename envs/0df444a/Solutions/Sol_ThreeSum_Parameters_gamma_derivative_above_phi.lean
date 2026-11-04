-- Prove2me | solution 1 for ThreeSum.Parameters.gamma_derivative_above_phi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:21.248694+00:00
-- url     : https://prove2.me/submissions/36093d7f-16a3-4942-a206-360cdf0033ef

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_log_two_upper
import Theorems.Thm_ThreeSum_Parameters_log_255_lower
import Theorems.Thm_ThreeSum_Parameters_neg_log_one_sub_lower

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    Real.log 2 * phiDeriv t ≤ Real.log (255 + t) - Real.log (1 - t) := by
  have hlog : Real.log 255 ≤ Real.log (255 + t) :=
    Real.log_le_log (by norm_num) (by linarith [ht.1])
  have hneg := neg_log_one_sub_lower ht.1 (by linarith [ht.2])
  have hpoly : 0 ≤ (36 / 25 : ℝ) * t + (18 / 25) * t ^ 2 := by
    nlinarith [ht.1, sq_nonneg t]
  have hprod := mul_le_mul_of_nonneg_right log_two_upper.le hpoly
  dsimp [phiDeriv]
  nlinarith [log_255_lower]
end ThreeSum.Parameters
