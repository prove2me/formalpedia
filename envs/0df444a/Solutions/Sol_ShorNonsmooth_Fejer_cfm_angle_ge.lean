-- Prove2me | solution 1 for ShorNonsmooth.Fejer.cfm_angle_ge
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-23T11:14:42.850019+00:00
-- url     : https://prove2.me/submissions/59e8b7dc-7d7b-4e23-91eb-03cd353c6e1b

import Theorems.Thm_ShorNonsmooth_Fejer_cfm_inner_direction_ge

open ShorNonsmooth.Fejer

private lemma beta_nonneg {n : ℕ} (a : ℝ) (ha : 0 ≤ a)
    (u v : EuclideanSpace ℝ (Fin n)) : 0 ≤ cfmBeta a u v := by
  unfold cfmBeta
  split_ifs with h
  · exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr ha) h.le) (sq_nonneg _)
  · rfl

private lemma corrected_norm_le {n : ℕ} (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2)
    (u v : EuclideanSpace ℝ (Fin n)) : ‖v + cfmBeta a u v • u‖ ≤ ‖v‖ := by
  unfold cfmBeta
  split_ifs with h
  · have hu : u ≠ 0 := by
      intro hz
      simp [hz] at h
    have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have heq : ‖v + (-a * inner ℝ u v / ‖u‖ ^ 2) • u‖ ^ 2 =
        ‖v‖ ^ 2 - a * (2 - a) * (inner ℝ u v) ^ 2 / ‖u‖ ^ 2 := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs, real_inner_comm v u]
      field_simp
      <;> ring
    have hdec : 0 ≤ a * (2 - a) * (inner ℝ u v) ^ 2 / ‖u‖ ^ 2 := by
      exact div_nonneg (mul_nonneg (mul_nonneg ha0 (sub_nonneg.mpr ha2)) (sq_nonneg _)) (sq_nonneg _)
    nlinarith [norm_nonneg (v + (-a * inner ℝ u v / ‖u‖ ^ 2) • u), norm_nonneg v]
  · simp

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (xstar : EuclideanSpace ℝ (Fin n))
    (hmin : ∀ y, f xstar ≤ f y)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x))
    (γ α : ℕ → ℝ) (hγ : ∀ k, 0 < γ k ∧ γ k ≤ 1) (hα : ∀ k, 0 ≤ α k ∧ α k ≤ 2)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (hs0 : s 0 = g (x 0))
    (hx : ∀ k, x (k + 1) = x k - cfmStepsize f (f xstar) (γ k) (x k) (s k) • s k)
    (hs : ∀ k, s (k + 1) = g (x (k + 1)) + cfmBeta (α (k + 1)) (s k) (g (x (k + 1))) • s k) :
    ∀ k, s k ≠ 0 → g (x k) ≠ 0 →
      inner ℝ (x k - xstar) (s k) / ‖s k‖ ≥ inner ℝ (x k - xstar) (g (x k)) / ‖g (x k)‖  := by
  let β : ℕ → ℝ := fun k => match k with
    | 0 => 0
    | j + 1 => cfmBeta (α (j + 1)) (s j) (g (x (j + 1)))
  have hβ : ∀ k, 0 ≤ β k := by
    intro k
    cases k with
    | zero => exact le_refl 0
    | succ j => exact beta_nonneg _ (hα (j + 1)).1 _ _
  have hd := cfm_inner_direction_ge f hf xstar hmin g hg γ β hγ hβ x s hs0 hx hs
  have hn : ∀ k, ‖s k‖ ≤ ‖g (x k)‖ := by
    intro k
    cases k with
    | zero => rw [hs0]
    | succ j =>
      rw [hs j]
      exact corrected_norm_le _ (hα (j + 1)).1 (hα (j + 1)).2 _ _
  intro k hsk hgk
  have hnonneg : 0 ≤ inner ℝ (x k - xstar) (g (x k)) := by
    have h := hg (x k) xstar
    rw [inner_sub_right] at h
    rw [real_inner_comm, inner_sub_right]
    linarith [hmin (x k)]
  exact (div_le_div_of_nonneg_left hnonneg (norm_pos_iff.mpr hsk) (hn k)).trans
    (div_le_div_of_nonneg_right (hd k) (norm_nonneg _))

