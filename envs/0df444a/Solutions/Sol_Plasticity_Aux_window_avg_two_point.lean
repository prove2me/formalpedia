-- Prove2me | solution 1 for Plasticity.Aux.window_avg_two_point
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T08:12:27.770879+00:00
-- url     : https://prove2.me/submissions/6d4e30c9-2ca4-44c3-886f-980942ac471e

import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Sol_Plasticity_Aux_window_avg_two_point

/-- A Lipschitz bound in absolute-value form gives continuity. -/
lemma cont_of_lip {φ : ℝ → ℝ} {L : ℝ} (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|) :
    Continuous φ := by
  have : LipschitzWith (Real.toNNReal L) φ := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq]
    calc |φ x - φ y| ≤ L * |x - y| := hφ x y
      _ ≤ (Real.toNNReal L : ℝ) * |x - y| := by
        gcongr
        exact Real.le_coe_toNNReal L
  exact this.continuous

/-- Integral over `[a, a + t]` against the left endpoint value. -/
lemma endpoint_left {φ : ℝ → ℝ} {L : ℝ} (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|)
    (a t : ℝ) (ht : 0 ≤ t) :
    |(∫ x in a..a + t, φ x) - t * φ a| ≤ L * t ^ 2 / 2 := by
  have hc := cont_of_lip hφ
  have hab : a ≤ a + t := by linarith
  have h1 : (∫ x in a..a + t, φ x) - t * φ a = ∫ x in a..a + t, (φ x - φ a) := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [h1]
  calc |∫ x in a..a + t, (φ x - φ a)| ≤ ∫ x in a..a + t, |φ x - φ a| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ x in a..a + t, L * (x - a) := by
        apply intervalIntegral.integral_mono_on hab
        · exact (by fun_prop : Continuous fun x => |φ x - φ a|).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun x => L * (x - a)).intervalIntegrable _ _
        · intro x hx
          have := hφ x a
          rwa [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - a)] at this
    _ = L * t ^ 2 / 2 := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub ((continuous_id' (X := ℝ)).intervalIntegrable _ _)
            intervalIntegrable_const, integral_id, intervalIntegral.integral_const, smul_eq_mul]
        ring

/-- Integral over `[a - t, a]` against the right endpoint value. -/
lemma endpoint_right {φ : ℝ → ℝ} {L : ℝ} (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|)
    (a t : ℝ) (ht : 0 ≤ t) :
    |(∫ x in a - t..a, φ x) - t * φ a| ≤ L * t ^ 2 / 2 := by
  have hc := cont_of_lip hφ
  have hab : a - t ≤ a := by linarith
  have h1 : (∫ x in a - t..a, φ x) - t * φ a = ∫ x in a - t..a, (φ x - φ a) := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [h1]
  calc |∫ x in a - t..a, (φ x - φ a)| ≤ ∫ x in a - t..a, |φ x - φ a| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ x in a - t..a, L * (a - x) := by
        apply intervalIntegral.integral_mono_on hab
        · exact (by fun_prop : Continuous fun x => |φ x - φ a|).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun x => L * (a - x)).intervalIntegrable _ _
        · intro x hx
          have := hφ x a
          rwa [abs_sub_comm x a, abs_of_nonneg (by linarith [hx.2] : 0 ≤ a - x)] at this
    _ = L * t ^ 2 / 2 := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub intervalIntegrable_const
            ((continuous_id' (X := ℝ)).intervalIntegrable _ _), integral_id, intervalIntegral.integral_const,
          smul_eq_mul]
        ring

/-- Shifting the window to the left by `t ≥ 0`. -/
lemma shift_sub {φ : ℝ → ℝ} {L : ℝ} (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|)
    (a b t : ℝ) (ht : 0 ≤ t) :
    (∫ s in a..b, φ (s - t)) - (∫ s in a..b, φ s) ≤ t * (φ a - φ b) + L * t ^ 2 := by
  have hc := cont_of_lip hφ
  rw [intervalIntegral.integral_comp_sub_right φ t,
    intervalIntegral.integral_interval_sub_interval_comm (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have e1 := abs_le.mp (endpoint_right hφ a t ht)
  have e2 := abs_le.mp (endpoint_right hφ b t ht)
  linarith [e1.1, e1.2, e2.1, e2.2]

/-- Shifting the window to the right by `u ≥ 0`. -/
lemma shift_add {φ : ℝ → ℝ} {L : ℝ} (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|)
    (a b u : ℝ) (hu : 0 ≤ u) :
    (∫ s in a..b, φ (s + u)) - (∫ s in a..b, φ s) ≤ u * (φ b - φ a) + L * u ^ 2 := by
  have hc := cont_of_lip hφ
  rw [intervalIntegral.integral_comp_add_right φ u,
    intervalIntegral.integral_interval_sub_interval_comm (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_symm a, intervalIntegral.integral_symm b]
  have e1 := abs_le.mp (endpoint_left hφ a u hu)
  have e2 := abs_le.mp (endpoint_left hφ b u hu)
  linarith [e1.1, e1.2, e2.1, e2.2]

end Sol_Plasticity_Aux_window_avg_two_point

theorem solution (g : ℝ → ℝ) (hg : LipschitzWith 1 g) (h t u K : ℝ)
    (hh : 0 < h) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hK : ∀ s ∈ Set.Icc (-h) h, K ≤ u * g (s - t) + t * g (s + u) - (t + u) * g s) :
    K ≤ (u * t ^ 2 + t * u ^ 2) / (2 * h) := by
  have hφ : ∀ x y, |g x - g y| ≤ 1 * |x - y| := by
    intro x y
    have := hg.dist_le_mul x y
    simpa [Real.dist_eq] using this
  have hc : Continuous g := hg.continuous
  have hhh : -h ≤ h := by linarith
  -- Average the pointwise inequality over the window `[-h, h]`.
  have hint : (∫ _ in (-h)..h, K) ≤
      ∫ s in (-h)..h, (u * g (s - t) + t * g (s + u) - (t + u) * g s) :=
    intervalIntegral.integral_mono_on hhh intervalIntegrable_const
      ((by fun_prop : Continuous fun s => u * g (s - t) + t * g (s + u) - (t + u) * g s).intervalIntegrable
        _ _) hK
  have hsplit : (∫ s in (-h)..h, (u * g (s - t) + t * g (s + u) - (t + u) * g s)) =
      u * (∫ s in (-h)..h, g (s - t)) + t * (∫ s in (-h)..h, g (s + u)) -
        (t + u) * ∫ s in (-h)..h, g s := by
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hsplit, intervalIntegral.integral_const, smul_eq_mul] at hint
  -- The shifted averages differ from the centred one by a boundary term plus a square.
  have w1 := Sol_Plasticity_Aux_window_avg_two_point.shift_sub hφ (-h) h t ht
  have w2 := Sol_Plasticity_Aux_window_avg_two_point.shift_add hφ (-h) h u hu
  have m1 := mul_le_mul_of_nonneg_left w1 hu
  have m2 := mul_le_mul_of_nonneg_left w2 ht
  have key : (2 * h) * K ≤ u * t ^ 2 + t * u ^ 2 := by
    nlinarith
  rw [le_div_iff₀ (by positivity)]
  linarith
