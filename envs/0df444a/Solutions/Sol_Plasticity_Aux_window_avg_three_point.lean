-- Prove2me | solution 1 for Plasticity.Aux.window_avg_three_point
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T08:12:59.332804+00:00
-- url     : https://prove2.me/submissions/8a5b32f5-ec9e-4fac-8244-0bc2b2688a41

import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Sol_Plasticity_Aux_window_avg_three_point

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

/-- Integrals of two continuous functions that stay within `C` of each other. -/
lemma abs_integral_sub_le {f f' : ℝ → ℝ} (hf : Continuous f) (hf' : Continuous f') {C : ℝ}
    (hC : ∀ x, |f x - f' x| ≤ C) (a b : ℝ) :
    |(∫ x in a..b, f x) - ∫ x in a..b, f' x| ≤ C * |b - a| := by
  rw [← intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hf'.intervalIntegrable _ _)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := C)
    (f := fun x => f x - f' x) (fun x _ => by rw [Real.norm_eq_abs]; exact hC x)
  rw [Real.norm_eq_abs] at this
  exact this

/-- A window integral of a family that is `1`-Lipschitz in the parameter is
`2h`-Lipschitz in the parameter. -/
lemma window_lip {k : ℝ → ℝ → ℝ} (hk : ∀ r, Continuous fun s => k s r)
    (hkr : ∀ s r r', |k s r - k s r'| ≤ |r - r'|) {h : ℝ} (hh : 0 < h) (x y : ℝ) :
    |(∫ s in (-h)..h, k s x) - ∫ s in (-h)..h, k s y| ≤ (2 * h) * |x - y| := by
  have := abs_integral_sub_le (hk x) (hk y) (fun s => hkr s x y) (-h) h
  have e : |h - -h| = 2 * h := by rw [abs_of_pos (by linarith)]; ring
  rw [e] at this
  linarith

end Sol_Plasticity_Aux_window_avg_three_point

theorem solution (g : ℝ → ℝ → ℝ)
    (hg : ∀ s r s' r' : ℝ, |g s r - g s' r'| ≤ |s - s'| + |r - r'|) (h t K : ℝ)
    (hh : 0 < h) (ht : 0 ≤ t)
    (hK : ∀ s ∈ Set.Icc (-h) h, ∀ r ∈ Set.Icc (-h) h,
      K ≤ g (s - t) r + g s (r - t) + g (s + t) (r + t) - 3 * g s r) :
    K ≤ 3 * t ^ 2 / h := by
  have hhh : -h ≤ h := by linarith
  -- Separate Lipschitz bounds in each variable.
  have hs1 : ∀ r x y, |g x r - g y r| ≤ |x - y| := by
    intro r x y
    have := hg x r y r
    simpa using this
  have hr1 : ∀ s x y, |g s x - g s y| ≤ |x - y| := by
    intro s x y
    have := hg s x s y
    simpa using this
  have hsL : ∀ r x y, |g x r - g y r| ≤ 1 * |x - y| := by
    intro r x y; rw [one_mul]; exact hs1 r x y
  have hcs : ∀ r, Continuous fun x => g x r := fun r =>
    Sol_Plasticity_Aux_window_avg_three_point.cont_of_lip (hsL r)
  have hcsub : ∀ r, Continuous fun s => g (s - t) r := fun r =>
    (hcs r).comp (continuous_sub_right t)
  have hcadd : ∀ r, Continuous fun s => g (s + t) r := fun r =>
    (hcs r).comp (continuous_add_const t)
  -- Window integrals in the first variable.
  obtain ⟨P, hP⟩ : ∃ P : ℝ → ℝ, ∀ r, P r = ∫ s in (-h)..h, g (s - t) r := ⟨_, fun r => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → ℝ, ∀ r, Q r = ∫ s in (-h)..h, g s r := ⟨_, fun r => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, ∀ r, R r = ∫ s in (-h)..h, g (s + t) r := ⟨_, fun r => rfl⟩
  have hPl : ∀ x y, |P x - P y| ≤ (2 * h) * |x - y| := by
    intro x y
    rw [hP, hP]
    exact Sol_Plasticity_Aux_window_avg_three_point.window_lip (k := fun s r => g (s - t) r)
      hcsub (fun s r r' => hr1 (s - t) r r') hh x y
  have hQl : ∀ x y, |Q x - Q y| ≤ (2 * h) * |x - y| := by
    intro x y
    rw [hQ, hQ]
    exact Sol_Plasticity_Aux_window_avg_three_point.window_lip (k := fun s r => g s r)
      hcs (fun s r r' => hr1 s r r') hh x y
  have hRl : ∀ x y, |R x - R y| ≤ (2 * h) * |x - y| := by
    intro x y
    rw [hR, hR]
    exact Sol_Plasticity_Aux_window_avg_three_point.window_lip (k := fun s r => g (s + t) r)
      hcadd (fun s r r' => hr1 (s + t) r r') hh x y
  have hPc : Continuous P := Sol_Plasticity_Aux_window_avg_three_point.cont_of_lip hPl
  have hQc : Continuous Q := Sol_Plasticity_Aux_window_avg_three_point.cont_of_lip hQl
  have hRc : Continuous R := Sol_Plasticity_Aux_window_avg_three_point.cont_of_lip hRl
  -- Step 1: average the pointwise inequality in the first variable.
  have step1 : ∀ r ∈ Set.Icc (-h) h, (2 * h) * K ≤ P r + Q (r - t) + R (r + t) - 3 * Q r := by
    intro r hr0
    have c1 := hcsub r
    have c2 := hcs (r - t)
    have c3 := hcadd (r + t)
    have c4 := hcs r
    have hint : (∫ _ in (-h)..h, K) ≤
        ∫ s in (-h)..h, (g (s - t) r + g s (r - t) + g (s + t) (r + t) - 3 * g s r) :=
      intervalIntegral.integral_mono_on hhh intervalIntegrable_const
        ((by fun_prop : Continuous fun s =>
          g (s - t) r + g s (r - t) + g (s + t) (r + t) - 3 * g s r).intervalIntegrable _ _)
        (fun s hs => hK s hs r hr0)
    have hsplit :
        (∫ s in (-h)..h, (g (s - t) r + g s (r - t) + g (s + t) (r + t) - 3 * g s r)) =
          P r + Q (r - t) + R (r + t) - 3 * Q r := by
      simp only [hP, hQ, hR]
      rw [intervalIntegral.integral_sub, intervalIntegral.integral_add,
        intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
      all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
    rw [hsplit, intervalIntegral.integral_const, smul_eq_mul] at hint
    have e : h - -h = 2 * h := by ring
    rw [e] at hint
    exact hint
  -- Step 2: average again in the second variable.
  have hint2 : (∫ _ in (-h)..h, (2 * h) * K) ≤
      ∫ r in (-h)..h, (P r + Q (r - t) + R (r + t) - 3 * Q r) :=
    intervalIntegral.integral_mono_on hhh intervalIntegrable_const
      ((by fun_prop : Continuous fun r =>
        P r + Q (r - t) + R (r + t) - 3 * Q r).intervalIntegrable _ _) step1
  have hsplit2 : (∫ r in (-h)..h, (P r + Q (r - t) + R (r + t) - 3 * Q r)) =
      (∫ r in (-h)..h, P r) + (∫ r in (-h)..h, Q (r - t)) + (∫ r in (-h)..h, R (r + t)) -
        3 * ∫ r in (-h)..h, Q r := by
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_add,
      intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hsplit2, intervalIntegral.integral_const, smul_eq_mul] at hint2
  -- Step 3: the shifts in the first variable cost at most `2t²` for each `r`.
  have step3 : ∀ r, P r + R r - 2 * Q r ≤ 2 * t ^ 2 := by
    intro r
    have w1 := Sol_Plasticity_Aux_window_avg_three_point.shift_sub (hsL r) (-h) h t ht
    have w2 := Sol_Plasticity_Aux_window_avg_three_point.shift_add (hsL r) (-h) h t ht
    rw [hP, hQ, hR]
    linarith
  have hint3 : (∫ r in (-h)..h, (P r + R r - 2 * Q r)) ≤ ∫ _ in (-h)..h, 2 * t ^ 2 :=
    intervalIntegral.integral_mono_on hhh
      ((by fun_prop : Continuous fun r => P r + R r - 2 * Q r).intervalIntegrable _ _)
      intervalIntegrable_const (fun r _ => step3 r)
  have hsplit3 : (∫ r in (-h)..h, (P r + R r - 2 * Q r)) =
      (∫ r in (-h)..h, P r) + (∫ r in (-h)..h, R r) - 2 * ∫ r in (-h)..h, Q r := by
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul]
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hsplit3, intervalIntegral.integral_const, smul_eq_mul] at hint3
  -- Step 4: the shifts in the second variable, with Lipschitz constant `2h`.
  have w3 := Sol_Plasticity_Aux_window_avg_three_point.shift_sub hQl (-h) h t ht
  have w4 := Sol_Plasticity_Aux_window_avg_three_point.shift_add hRl (-h) h t ht
  -- Step 5: `Q` and `R` differ by at most `2ht`.
  have hQR : ∀ r, |Q r - R r| ≤ t * (2 * h) := by
    intro r
    rw [hQ, hR]
    have := Sol_Plasticity_Aux_window_avg_three_point.abs_integral_sub_le (hcs r) (hcadd r)
      (C := t) (fun s => by have := hs1 r s (s + t); simpa [abs_of_nonneg ht] using this) (-h) h
    have e : |h - -h| = 2 * h := by rw [abs_of_pos (by linarith)]; ring
    rw [e] at this
    exact this
  have q1 := abs_le.mp (hQR (-h))
  have q2 := abs_le.mp (hQR h)
  have m1 : t * (Q (-h) - R (-h)) ≤ t * (t * (2 * h)) := mul_le_mul_of_nonneg_left q1.2 ht
  have m2 : t * (R h - Q h) ≤ t * (t * (2 * h)) :=
    mul_le_mul_of_nonneg_left (by linarith [q2.1]) ht
  -- Combine: `4h²K ≤ 12ht²`.
  have key : (h - -h) * (2 * h * K) ≤ 12 * h * t ^ 2 := by
    nlinarith
  rw [le_div_iff₀ hh]
  nlinarith
