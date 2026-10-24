-- Prove2me | solution 1 for ShorNonsmooth.Fejer.polyak_linear_rate_sharp_minimum
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-23T11:10:34.865626+00:00
-- url     : https://prove2.me/submissions/73616625-5564-42bb-90d9-b43b25391ffe

import Theorems.Thm_ShorNonsmooth_Fejer_polyak_step_dist_sq_le

open ShorNonsmooth.Fejer
set_option maxHeartbeats 800000

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (xstar : EuclideanSpace ℝ (Fin n))
    (hmin : ∀ y, f xstar ≤ f y) (m L : ℝ) (hm : 0 < m)
    (hsharp : ∀ x, f x - f xstar ≥ m * ‖x - xstar‖)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x))
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hx : ∀ k, x (k + 1) = polyakStep f g (f xstar) γ (x k))
    (hL : ∀ z ∈ Metric.closedBall xstar ‖x 0 - xstar‖, ∀ v, ShorNonsmooth.AlmostDiff.IsSubgradient f z v → ‖v‖ ≤ L) :
    ∀ k : ℕ, ‖x (k + 1) - xstar‖ ≤
      Real.sqrt (1 - γ * (2 - γ) * m ^ 2 / L ^ 2) * ‖x k - xstar‖ := by
  have hA : 0 ≤ γ * (2 - γ) := le_of_lt (mul_pos hγ0 (sub_pos.mpr hγ2))
  have hstep (k : ℕ) (hne : x k ≠ xstar) :
      ‖x (k+1) - xstar‖ ^ 2 ≤ ‖x k - xstar‖ ^ 2 -
        γ * (2 - γ) * (f (x k) - f xstar)^2 / ‖g (x k)‖^2 := by
    have hr : 0 < ‖x k - xstar‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hgap : f xstar < f (x k) := by
      have := hsharp (x k)
      have := mul_pos hm hr
      linarith
    have hg0 : g (x k) ≠ 0 := by
      intro he
      have hh := hg (x k) xstar
      simp only [he, inner_zero_left] at hh
      linarith
    have hs := (polyak_step_dist_sq_le f hf (f xstar) γ hγ0 hγ2
      (x k) (g (x k)) xstar (hg (x k)) (by exact not_le.mpr hgap) (by change f xstar ≤ f xstar; exact le_rfl)).1
    rw [hx k, polyakStep, if_neg (not_or.mpr ⟨not_le.mpr hgap, hg0⟩)]
    exact hs
  have hmono (k : ℕ) : ‖x (k+1) - xstar‖ ≤ ‖x k - xstar‖ := by
    by_cases he : x k = xstar
    · simp [hx k, he, polyakStep]
    · have hs := hstep k he
      have hd : 0 ≤ γ * (2-γ) * (f (x k)-f xstar)^2 / ‖g (x k)‖^2 := by positivity
      nlinarith [norm_nonneg (x (k+1)-xstar), norm_nonneg (x k-xstar)]
  have hball (k : ℕ) : ‖x k - xstar‖ ≤ ‖x 0 - xstar‖ := by
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hmono k).trans ih
  intro k
  by_cases he : x k = xstar
  · simp [hx k, he, polyakStep]
  have hr : 0 < ‖x k - xstar‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hgap : 0 < f (x k) - f xstar := lt_of_lt_of_le (mul_pos hm hr) (hsharp (x k))
  have hg0 : g (x k) ≠ 0 := by
    intro he
    have hh := hg (x k) xstar
    simp only [he, inner_zero_left] at hh
    linarith
  have hgn : 0 < ‖g (x k)‖ := norm_pos_iff.mpr hg0
  have hbound : ‖g (x k)‖ ≤ L :=
    hL (x k) (by simpa [Metric.mem_closedBall, dist_eq_norm] using hball k) _ (hg (x k))
  have hLp : 0 < L := hgn.trans_le hbound
  have hgap2 : (m * ‖x k - xstar‖)^2 ≤ (f (x k) - f xstar)^2 := by
    exact pow_le_pow_left₀ (le_of_lt (mul_pos hm hr)) (hsharp (x k)) 2
  have hn2 : ‖g (x k)‖^2 ≤ L^2 := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have hratio : (m * ‖x k - xstar‖)^2 / L^2 ≤
      (f (x k)-f xstar)^2 / ‖g (x k)‖^2 :=
    (div_le_div_of_nonneg_right hgap2 (sq_nonneg L)).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hgn) hn2)
  have hmul := mul_le_mul_of_nonneg_left hratio hA
  have hs := hstep k he
  have hs' : ‖x (k+1)-xstar‖^2 ≤
      (1 - γ*(2-γ)*m^2/L^2) * ‖x k-xstar‖^2 := by
    calc
      _ ≤ ‖x k-xstar‖^2 - γ*(2-γ)*(f (x k)-f xstar)^2/‖g (x k)‖^2 := hs
      _ ≤ ‖x k-xstar‖^2 - γ*(2-γ)*((m*‖x k-xstar‖)^2/L^2) := by
        simpa only [mul_div_assoc] using sub_le_sub_left hmul (‖x k-xstar‖^2)
      _ = _ := by ring
  have hsqrt := mul_le_mul_of_nonneg_right
    (show (1-γ*(2-γ)*m^2/L^2) ≤ (Real.sqrt (1-γ*(2-γ)*m^2/L^2))^2 by rw [Real.sq_sqrt']; exact le_max_left _ _) (sq_nonneg ‖x k-xstar‖)
  have hnon : 0 ≤ Real.sqrt (1-γ*(2-γ)*m^2/L^2) * ‖x k-xstar‖ := by positivity
  nlinarith [norm_nonneg (x (k+1)-xstar)]

