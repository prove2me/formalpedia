-- Prove2me | solution 1 for PolicyGradTheory.LogBarrier.beck_gradient_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T12:30:25.610149+00:00
-- url     : https://prove2.me/submissions/dc6b2e63-649f-4258-960b-8a282528906f

import Mathlib

open scoped InnerProductSpace

set_option autoImplicit false

namespace PE2410

theorem line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫_ℝ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

/-- Lower quadratic bound for an `L`-smooth function. -/
theorem ascent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    F x + ⟪G x, y - x⟫_ℝ - L / 2 * ‖y - x‖ ^ 2 ≤ F y := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * ⟪G x, w⟫_ℝ + L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪G (x + t • w), w⟫_ℝ - ⟪G x, w⟫_ℝ
      + L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := line_deriv hF x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪G x, w⟫_ℝ) ⟪G x, w⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪G x, w⟫_ℝ
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).add h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : 0 ≤ ⟪G (x + c • w), w⟫_ℝ - ⟪G x, w⟫_ℝ + L / 2 * (2 * c) * ‖w‖ ^ 2 := by
    have e1 : ⟪G (x + c • w), w⟫_ℝ - ⟪G x, w⟫_ℝ = ⟪G (x + c • w) - G x, w⟫_ℝ := by
      rw [inner_sub_left]
    have e2 := neg_le_of_abs_le (abs_real_inner_le_norm (G (x + c • w) - G x) w)
    have e3 := hG (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖G (x + c • w) - G x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 0 ≤ g 1 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

theorem step {ι : Type*} [Fintype ι] (f : EuclideanSpace ℝ ι → ℝ) (β : ℝ)
    (hβ : 0 < β) (hf : Differentiable ℝ f)
    (hsmooth : ∀ x y, ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖) (z : EuclideanSpace ℝ ι) :
    f z + ‖gradient f z‖ ^ 2 / (2 * β) ≤ f (z + (1 / β) • gradient f z) := by
  have hF : ∀ x, HasGradientAt f (gradient f x) x := fun x => (hf x).hasGradientAt
  have h := ascent hF hsmooth z (z + (1 / β) • gradient f z)
  rw [add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / β)] at h
  have e : 1 / β * ‖gradient f z‖ ^ 2 - β / 2 * (1 / β * ‖gradient f z‖) ^ 2
      = ‖gradient f z‖ ^ 2 / (2 * β) := by
    field_simp; ring
  linarith

end PE2410

theorem solution {ι : Type*} [Fintype ι] (f : EuclideanSpace ℝ ι → ℝ) (β : ℝ)
    (hβ : 0 < β) (hf : Differentiable ℝ f)
    (hsmooth : ∀ x y, ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖)
    (M : ℝ) (hM : ∀ x, f x ≤ M) (x : ℕ → EuclideanSpace ℝ ι)
    (hx : ∀ t, x (t + 1) = x t + (1 / β) • gradient f (x t)) :
    ∀ T : ℕ, 0 < T → ∃ t < T,
      ‖gradient f (x t)‖ ≤ Real.sqrt (2 * β * (M - f (x 0))) / Real.sqrt T := by
  intro T hT
  have htel : ∀ n : ℕ, f (x 0) + (∑ t ∈ Finset.range n, ‖gradient f (x t)‖ ^ 2) / (2 * β)
      ≤ f (x n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := PE2410.step f β hβ hf hsmooth (x n)
      rw [← hx n] at hs
      rw [Finset.sum_range_succ, add_div]
      linarith
  by_contra hcon
  push_neg at hcon
  set S := Real.sqrt (2 * β * (M - f (x 0))) / Real.sqrt T with hS
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  have hM0 : 0 ≤ M - f (x 0) := by linarith [hM (x 0)]
  have hS0 : 0 ≤ S := by positivity
  have hS2 : S ^ 2 = 2 * β * (M - f (x 0)) / T := by
    rw [hS, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hTpos.le]
  have hlt : ∀ t ∈ Finset.range T, S ^ 2 < ‖gradient f (x t)‖ ^ 2 := by
    intro t ht
    have := hcon t (Finset.mem_range.mp ht)
    exact pow_lt_pow_left₀ this hS0 (by norm_num)
  have hsum : ∑ t ∈ Finset.range T, S ^ 2 < ∑ t ∈ Finset.range T, ‖gradient f (x t)‖ ^ 2 :=
    Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hT⟩ hlt
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hS2] at hsum
  have e : (T:ℝ) * (2 * β * (M - f (x 0)) / T) = 2 * β * (M - f (x 0)) := by
    field_simp
  rw [e] at hsum
  have h1 := htel T
  have h2 := hM (x T)
  have h3 : M - f (x 0) < (∑ t ∈ Finset.range T, ‖gradient f (x t)‖ ^ 2) / (2 * β) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  linarith
