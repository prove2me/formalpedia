-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_log_two_mul_pow_div_add_le_751b1dc9fd76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:41.574723+00:00
-- url     : https://prove2.me/submissions/1950c902-eb0b-4ed7-b9f8-840bff16aaf7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PMeanLogPlus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open Real MeasureTheory Filter Topology Set
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.LowerBound
theorem _root_.solution {a : ℕ} {k : ℝ} (ha : 1 ≤ a) (hk : 3 * (a : ℝ) ≤ k) :
    log (2 * 36 ^ a) / k + 1 / k ≤ 3 := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hk0 : 0 < k := by linarith
  have h2 : log 2 < 1 := by have := log_two_lt_d9; norm_num at this; linarith
  have h36 : log 36 < 4 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    have he : exp 4 = exp 1 ^ 4 := by rw [← exp_nat_mul]; norm_num
    have h := pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
    rw [he]; norm_num at h ⊢; linarith
  have hlog : log (2 * 36 ^ a) = log 2 + a * log 36 := by
    rw [log_mul (by norm_num) (by positivity), log_pow]
  rw [← add_div, div_le_iff₀ hk0, hlog]
  nlinarith
end GroundTheory.Heights₂.Heights.LowerBound
