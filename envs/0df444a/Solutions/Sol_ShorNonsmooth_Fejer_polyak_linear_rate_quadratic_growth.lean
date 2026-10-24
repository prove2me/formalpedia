-- Prove2me | solution 1 for ShorNonsmooth.Fejer.polyak_linear_rate_quadratic_growth
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-23T11:18:39.309152+00:00
-- url     : https://prove2.me/submissions/122f7211-e6e8-46de-be0f-03948ff86cc3

import Theorems.Thm_ShorNonsmooth_Fejer_polyak_step_dist_sq_le
open Filter Topology
namespace ShorNonsmooth.Fejer
private theorem subgradient_eq_gradient {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (z v : EuclideanSpace ℝ (Fin n)) (hd : DifferentiableAt ℝ f z)
    (hv : ShorNonsmooth.AlmostDiff.IsSubgradient f z v) : v = gradient f z := by
  let l := InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) v
  have hmin : IsLocalMin (fun y => f y - l y) z := by
    apply Filter.Eventually.of_forall
    intro y
    have h := hv y
    simp only [inner_sub_right] at h
    change f z - inner ℝ v z ≤ f y - inner ℝ v y
    linarith
  have heq := (hd.hasFDerivAt.sub l.hasFDerivAt).fderiv
  have hz := hmin.fderiv_eq_zero
  change fderiv ℝ (f - ⇑l) z = 0 at hz
  rw [heq] at hz
  have hfd : fderiv ℝ f z = l := sub_eq_zero.mp hz
  simp only [gradient, hfd, l, LinearIsometryEquiv.symm_apply_apply]


/-- Shor (1985), p. 38, Theorem 2.12. Let `f` be convex on `E_n` with minimum point `x*`,
`f* = f(x*)`, satisfying `f(x) - f* ≥ m ‖x - x*‖²` for some `m > 0` and all `x`, and let `f` be
differentiable with gradient Lipschitz continuous with constant `L > 0` on the ball
`‖x - x*‖ ≤ ‖x₀ - x*‖`. Then Polyak's method (2.32) with `c = f*` and `0 < γ < 2`, for any
subgradient selection, satisfies `‖x_k - x*‖ ≤ q^k ‖x₀ - x*‖` for all `k`, where
`q = (1 - γ(2 - γ) m² / L²)^{1/2} < 1`. -/
theorem polyak_linear_rate_quadratic_growth {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (xstar : EuclideanSpace ℝ (Fin n))
    (hmin : ∀ y, f xstar ≤ f y) (m L : ℝ) (hm : 0 < m) (hL : 0 < L)
    (hgrowth : ∀ x, f x - f xstar ≥ m * ‖x - xstar‖ ^ 2)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x))
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hx : ∀ k, x (k + 1) = polyakStep f g (f xstar) γ (x k))
    (hdiff : ∀ z ∈ Metric.closedBall xstar ‖x 0 - xstar‖, DifferentiableAt ℝ f z)
    (hLip : ∀ z ∈ Metric.closedBall xstar ‖x 0 - xstar‖,
      ∀ w ∈ Metric.closedBall xstar ‖x 0 - xstar‖,
        ‖gradient f z - gradient f w‖ ≤ L * ‖z - w‖) :
    (∀ k : ℕ, ‖x k - xstar‖ ≤
        Real.sqrt (1 - γ * (2 - γ) * m ^ 2 / L ^ 2) ^ k * ‖x 0 - xstar‖) ∧
      Real.sqrt (1 - γ * (2 - γ) * m ^ 2 / L ^ 2) < 1 := by
  have hA : 0 < γ * (2 - γ) := mul_pos hγ0 (sub_pos.mpr hγ2)
  let q := Real.sqrt (1 - γ * (2 - γ) * m ^ 2 / L ^ 2)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q < 1 := by
    apply (Real.sqrt_lt' zero_lt_one).2
    have hp : 0 < γ * (2 - γ) * m ^ 2 / L ^ 2 := by positivity
    nlinarith
  have hqsq : 1 - γ * (2 - γ) * m ^ 2 / L ^ 2 ≤ q ^ 2 := by
    by_cases h : 0 ≤ 1 - γ * (2 - γ) * m ^ 2 / L ^ 2
    · exact le_of_eq (Real.sq_sqrt h).symm
    · exact le_trans (le_of_not_ge h) (sq_nonneg q)
  have hgrad0 : gradient f xstar = 0 := by
    have hh : IsLocalMin f xstar := Filter.Eventually.of_forall hmin
    simp [gradient, hh.fderiv_eq_zero]
  have hstarball : xstar ∈ Metric.closedBall xstar ‖x 0 - xstar‖ := by
    simp [norm_nonneg]
  have hstep : ∀ z, ‖z - xstar‖ ≤ ‖x 0 - xstar‖ →
      ‖polyakStep f g (f xstar) γ z - xstar‖ ≤ q * ‖z - xstar‖ := by
    intro z hz
    have hzb : z ∈ Metric.closedBall xstar ‖x 0 - xstar‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hggrad := subgradient_eq_gradient f z (g z) (hdiff z hzb) (hg z)
    have hnorm : ‖g z‖ ≤ L * ‖z - xstar‖ := by
      simpa only [← hggrad, hgrad0, sub_zero] using hLip z hzb xstar hstarball
    by_cases hzero : z = xstar
    · subst z
      simp [polyakStep, q]
    have hr : 0 < ‖z - xstar‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzero)
    have hd : 0 < f z - f xstar := lt_of_lt_of_le (by positivity) (hgrowth z)
    have hn : g z ≠ 0 := by
      intro he
      have hh := hg z xstar
      simp only [he, inner_zero_left] at hh
      linarith
    have hgn : 0 < ‖g z‖ := norm_pos_iff.mpr hn
    have hdec := (polyak_step_dist_sq_le f hf (f xstar) γ hγ0 hγ2 z (g z)
      xstar (hg z) (show z ∉ levelSet f (f xstar) by change ¬ f z ≤ f xstar; linarith)
      (show xstar ∈ levelSet f (f xstar) by exact le_refl (f xstar))).1
    have hratio : m * ‖z - xstar‖ / L ≤ (f z - f xstar) / ‖g z‖ := by
      apply (div_le_div_iff₀ hL hgn).2
      have ha := mul_le_mul_of_nonneg_left hnorm (le_of_lt (mul_pos hm hr))
      have hb := mul_le_mul_of_nonneg_left (hgrowth z) hL.le
      nlinarith
    have hratio2 : m ^ 2 / L ^ 2 * ‖z - xstar‖ ^ 2 ≤
        (f z - f xstar) ^ 2 / ‖g z‖ ^ 2 := by
      have hh := sq_le_sq₀ (by positivity : 0 ≤ m * ‖z - xstar‖ / L)
        (by positivity : 0 ≤ (f z - f xstar) / ‖g z‖)
      have hh2 := hh.mpr hratio
      calc
        m ^ 2 / L ^ 2 * ‖z - xstar‖ ^ 2 = (m * ‖z - xstar‖ / L) ^ 2 := by ring
        _ ≤ ((f z - f xstar) / ‖g z‖) ^ 2 := hh2
        _ = (f z - f xstar) ^ 2 / ‖g z‖ ^ 2 := by ring
    have hb := mul_le_mul_of_nonneg_left hratio2 hA.le
    have hc := mul_le_mul_of_nonneg_right hqsq (sq_nonneg ‖z - xstar‖)
    have hst : polyakStep f g (f xstar) γ z =
        z - (γ * (f z - f xstar) / ‖g z‖ ^ 2) • g z := by
      simp [polyakStep, hn, show ¬ f z ≤ f xstar by linarith]
    rw [hst]
    have hle : ‖z - (γ * (f z - f xstar) / ‖g z‖ ^ 2) • g z - xstar‖ ^ 2 ≤
        (q * ‖z - xstar‖) ^ 2 := by
      calc
        _ ≤ ‖z - xstar‖ ^ 2 - γ * (2 - γ) * (f z - f xstar) ^ 2 / ‖g z‖ ^ 2 := hdec
        _ = ‖z - xstar‖ ^ 2 - γ * (2 - γ) * ((f z - f xstar) ^ 2 / ‖g z‖ ^ 2) := by ring
        _ ≤ ‖z - xstar‖ ^ 2 - γ * (2 - γ) * (m ^ 2 / L ^ 2 * ‖z - xstar‖ ^ 2) := sub_le_sub_left hb _
        _ = (1 - γ * (2 - γ) * m ^ 2 / L ^ 2) * ‖z - xstar‖ ^ 2 := by ring
        _ ≤ q ^ 2 * ‖z - xstar‖ ^ 2 := hc
        _ = (q * ‖z - xstar‖) ^ 2 := by ring
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq0 hr.le)).1 hle
  constructor
  · intro k
    have hall : ∀ k : ℕ, ‖x k - xstar‖ ≤ q ^ k * ‖x 0 - xstar‖ ∧
        ‖x k - xstar‖ ≤ ‖x 0 - xstar‖ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hs := hstep (x k) ih.2
        rw [← hx k] at hs
        constructor
        · calc
            ‖x (k + 1) - xstar‖ ≤ q * ‖x k - xstar‖ := hs
            _ ≤ q * (q ^ k * ‖x 0 - xstar‖) := mul_le_mul_of_nonneg_left ih.1 hq0
            _ = q ^ (k + 1) * ‖x 0 - xstar‖ := by rw [pow_succ]; ring
        · calc
            ‖x (k + 1) - xstar‖ ≤ q * ‖x k - xstar‖ := hs
            _ ≤ 1 * ‖x k - xstar‖ := mul_le_mul_of_nonneg_right hq1.le (norm_nonneg _)
            _ ≤ ‖x 0 - xstar‖ := by simpa using ih.2
    exact (hall k).1
  · exact hq1
end ShorNonsmooth.Fejer





open ShorNonsmooth.Fejer

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (xstar : EuclideanSpace ℝ (Fin n))
    (hmin : ∀ y, f xstar ≤ f y) (m L : ℝ) (hm : 0 < m) (hL : 0 < L)
    (hgrowth : ∀ x, f x - f xstar ≥ m * ‖x - xstar‖ ^ 2)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x))
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hx : ∀ k, x (k + 1) = polyakStep f g (f xstar) γ (x k))
    (hdiff : ∀ z ∈ Metric.closedBall xstar ‖x 0 - xstar‖, DifferentiableAt ℝ f z)
    (hLip : ∀ z ∈ Metric.closedBall xstar ‖x 0 - xstar‖,
      ∀ w ∈ Metric.closedBall xstar ‖x 0 - xstar‖,
        ‖gradient f z - gradient f w‖ ≤ L * ‖z - w‖) :
    (∀ k : ℕ, ‖x k - xstar‖ ≤
        Real.sqrt (1 - γ * (2 - γ) * m ^ 2 / L ^ 2) ^ k * ‖x 0 - xstar‖) ∧
      Real.sqrt (1 - γ * (2 - γ) * m ^ 2 / L ^ 2) < 1 := by
  exact ShorNonsmooth.Fejer.polyak_linear_rate_quadratic_growth f hf xstar hmin m L hm hL
    hgrowth γ hγ0 hγ2 g hg x hx hdiff hLip
