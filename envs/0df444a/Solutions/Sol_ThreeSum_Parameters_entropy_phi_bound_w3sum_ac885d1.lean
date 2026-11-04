-- Prove2me | solution 1 for ThreeSum.Parameters.entropy_phi_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:45.063523+00:00
-- url     : https://prove2.me/submissions/a0af610c-07db-4371-aa40-c6529c0f46f9

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_tangentA_bound
import Theorems.Thm_ThreeSum_Parameters_tangentAB_bound
import Theorems.Thm_ThreeSum_Parameters_tangent_left_margin
import Theorems.Thm_ThreeSum_Parameters_tangent_right_margin
import Theorems.Thm_ThreeSum_Parameters_entropy_tangent
import Theorems.Thm_ThreeSum_Parameters_phi_above_tangent

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    entropy t < entropyRatio * (1 + phi t) := by
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  have hl := lt_trans tangentA_bound tangent_left_margin
  have hr := lt_trans tangentAB_bound tangent_right_margin
  have hline : tangentA + tangentB * t <
      entropyRatio * (1 + phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint) := by
    by_cases hhalf : t < 1 / 2
    · have hp := mul_lt_mul_of_pos_left hl (by linarith : 0 < 1 - 2 * t)
      have hq := mul_le_mul_of_nonneg_left hr.le (by linarith [ht.1] : 0 ≤ 2 * t)
      nlinarith
    · have heq : t = 1 / 2 := by linarith [ht.2]
      rw [heq]
      simpa [div_eq_mul_inv] using hr
  have hpoly := mul_le_mul_of_nonneg_left (phi_above_tangent ht.1)
    (by norm_num [entropyRatio] : 0 ≤ entropyRatio)
  have hent := entropy_tangent ht1
  linarith
end ThreeSum.Parameters
