-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.exp_ge_one_add_add_sq_div_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:44.315046+00:00
-- url     : https://prove2.me/submissions/74fc7186-f2cf-4cfb-852b-2f1c9283ccff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {u : ℝ} (hu : |u| ≤ 1) :
    1 + u + u ^ 2 / 3 ≤ Real.exp u := by
  have hb := Real.exp_bound hu (n := 5) (by norm_num)
  have h1 : -(|u| ^ 5 * ((Nat.succ 5 : ℝ) / ((Nat.factorial 5 : ℝ) * 5))) ≤
      Real.exp u - ∑ i ∈ Finset.range 5, u ^ i / (Nat.factorial i : ℝ) := (abs_le.mp hb).1
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1
  have hu2 : |u| ^ 5 ≤ u ^ 2 := by
    have h0 : 0 ≤ |u| := abs_nonneg u
    have h3 : |u| ^ 3 ≤ 1 := pow_le_one₀ h0 hu
    calc |u| ^ 5 = |u| ^ 2 * |u| ^ 3 := by ring
      _ ≤ |u| ^ 2 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = u ^ 2 := by rw [mul_one, sq_abs]
  have hlo : -1 ≤ u := (abs_le.mp hu).1
  have hq : 0 ≤ (u + 1) * (u + 3) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonneg (sq_nonneg u) hq, sq_nonneg u]
end ReciprocityTheory.ChartRestriction.DS.S7
