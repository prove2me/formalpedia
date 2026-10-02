-- Prove2me | solution 1 for ShorNonsmooth.Ellipsoid.ball_field_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:24:13.276517+00:00
-- url     : https://prove2.me/submissions/ef73fe2e-eb2f-4892-b2fd-eab3608f2330

import Mathlib

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (gf : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hgf : ∀ x y : EuclideanSpace ℝ (Fin n), f y - f x ≥ inner ℝ (gf x) (y - x))
    (x₀ xstar : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (hxstar : xstar ∈ Metric.closedBall x₀ R)
    (hmin : ∀ x ∈ Metric.closedBall x₀ R, f xstar ≤ f x)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg_in : ∀ x ∈ Metric.closedBall x₀ R, g x = gf x)
    (hg_out : ∀ x ∉ Metric.closedBall x₀ R, g x = ‖x - x₀‖⁻¹ • (x - x₀)) :
    ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ inner ℝ (g x) (x - xstar) := by
  intro x
  by_cases hx : x ∈ Metric.closedBall x₀ R
  · rw [hg_in x hx]
    have h1 := hgf x xstar
    have h2 := hmin x hx
    have h3 : inner ℝ (gf x) (x - xstar) = - inner ℝ (gf x) (xstar - x) := by
      rw [← inner_neg_right, neg_sub]
    rw [h3]
    linarith
  · rw [hg_out x hx, real_inner_smul_left]
    have hxs : ‖xstar - x₀‖ ≤ R := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hxstar; exact hxstar
    have hxo : R < ‖x - x₀‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hx; exact hx
    have hpos : 0 < ‖x - x₀‖ := lt_of_le_of_lt ((norm_nonneg _).trans hxs) hxo
    have hsplit : x - xstar = (x - x₀) - (xstar - x₀) := by abel
    have hcs : inner ℝ (x - x₀) (xstar - x₀) ≤ ‖x - x₀‖ * ‖xstar - x₀‖ :=
      real_inner_le_norm _ _
    have hkey : 0 ≤ inner ℝ (x - x₀) (x - xstar) := by
      rw [hsplit, inner_sub_right, real_inner_self_eq_norm_sq]
      nlinarith
    exact mul_nonneg (inv_nonneg.mpr hpos.le) hkey
