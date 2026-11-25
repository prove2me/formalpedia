-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.tendsto_radK_boundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:44:54.264462+00:00
-- url     : https://prove2.me/submissions/ed2729db-0244-4825-9ff7-4053b7ca6eb6

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Set Real Filter Topology
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (m : ℕ) :
    Tendsto (fun r : ℝ => -(1 / 2) * (r ^ (m + 1) * (r * log r) * exp (-r ^ 2))) atTop (𝓝 0) := by
  have hA : Tendsto (fun r : ℝ => (r ^ 2) ^ (m + 3) * exp (-(r ^ 2))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (m + 3)).comp (tendsto_pow_atTop two_ne_zero)
  refine squeeze_zero_norm' ?_ hA
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr
  have hr0 : 0 < r := by linarith
  have hl0 : 0 ≤ log r := Real.log_nonneg hr
  have hl : log r ≤ r := (Real.log_le_sub_one_of_pos hr0).trans (by linarith)
  have he := exp_pos (-r ^ 2)
  have hp : r ^ (m + 3) ≤ (r ^ 2) ^ (m + 3) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hr (by omega)
  have nn : 0 ≤ r ^ (m + 1) * (r * log r) * exp (-r ^ 2) :=
    mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hr0.le hl0)) he.le
  have key : r ^ (m + 1) * (r * log r) * exp (-r ^ 2) ≤ (r ^ 2) ^ (m + 3) * exp (-(r ^ 2)) := by
    calc r ^ (m + 1) * (r * log r) * exp (-r ^ 2) ≤ r ^ (m + 1) * (r * r) * exp (-r ^ 2) := by
          gcongr
      _ = r ^ (m + 3) * exp (-r ^ 2) := by ring
      _ ≤ (r ^ 2) ^ (m + 3) * exp (-(r ^ 2)) := mul_le_mul_of_nonneg_right hp he.le
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith
end ReciprocityTheory.MultiplicativeHeights
