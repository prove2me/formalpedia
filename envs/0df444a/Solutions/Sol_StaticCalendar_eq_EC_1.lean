-- Prove2me | solution 1 for StaticCalendar.eq_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:46:04.24602+00:00
-- url     : https://prove2.me/submissions/831dfbe1-f002-486a-8bc1-49f98b4b4bef

import Mathlib
import Definitions.Def_StaticCalendar_binomMinExp

open MeasureTheory

open StaticCalendar in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc (0 : ℝ) 1)
    (c : ℝ) (hc : 0 ≤ c) :
    binomMinExp 1 (∫ y, y ∂μ) c ≤ ∫ y, min c y ∂μ := by
  have hb : ∀ p : ℝ, binomMinExp 1 p c = p * min c 1 := by
    intro p
    simp only [binomMinExp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
      Nat.choose_one_right, Nat.cast_zero, Nat.cast_one, pow_zero, pow_one, Nat.sub_zero,
      Nat.sub_self, min_eq_right hc]
    ring
  rw [hb, mul_comm, ← integral_const_mul]
  have hid : Integrable (fun y : ℝ => y) μ := by
    refine Integrable.of_bound aestronglyMeasurable_id 1 ?_
    filter_upwards [hμ] with y hy
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hy.1, hy.2]
  have hmin : Integrable (fun y : ℝ => min c y) μ := by
    refine Integrable.of_bound (continuous_const.min continuous_id).aestronglyMeasurable 1 ?_
    filter_upwards [hμ] with y hy
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := le_min hc hy.1
      linarith
    · have := min_le_right c y
      linarith [hy.2]
  apply integral_mono_ae (hid.const_mul _) hmin
  filter_upwards [hμ] with y hy
  have hm0 : 0 ≤ min c 1 := le_min hc zero_le_one
  apply le_min
  · nlinarith [min_le_left c 1, hy.1, hy.2]
  · nlinarith [min_le_right c 1, hy.1, hy.2]
