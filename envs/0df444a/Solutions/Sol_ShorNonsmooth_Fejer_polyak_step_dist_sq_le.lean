-- Prove2me | solution 1 for ShorNonsmooth.Fejer.polyak_step_dist_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-20T14:13:52.541662+00:00
-- url     : https://prove2.me/submissions/aa00476a-22a6-4c56-8f1a-0fc4170c030a

import Definitions.Def_ShorNonsmooth_Fejer_PolyakMethod

open ShorNonsmooth.Fejer

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (c γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (xk gk y : EuclideanSpace ℝ (Fin n)) (hgk : ShorNonsmooth.AlmostDiff.IsSubgradient f xk gk)
    (hxk : xk ∉ levelSet f c) (hy : y ∈ levelSet f c) :
    ‖xk - (γ * (f xk - c) / ‖gk‖ ^ 2) • gk - y‖ ^ 2 ≤
        ‖xk - y‖ ^ 2 - γ * (2 - γ) * (f xk - c) ^ 2 / ‖gk‖ ^ 2 ∧
      ‖xk - y‖ ^ 2 - γ * (2 - γ) * (f xk - c) ^ 2 / ‖gk‖ ^ 2 < ‖xk - y‖ ^ 2  := by
  have hx : c < f xk := lt_of_not_ge hxk
  have hyc : f y ≤ c := hy
  have hd : 0 < f xk - c := sub_pos.mpr hx
  have hinner : f xk - c ≤ inner ℝ (xk - y) gk := by
    have h := hgk y
    rw [inner_sub_right, real_inner_comm y gk, real_inner_comm xk gk] at h
    rw [inner_sub_left]
    linarith
  have hg : gk ≠ 0 := by
    intro hz
    simp only [hz, inner_zero_right] at hinner
    linarith
  have hnorm : 0 < ‖gk‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
  have ht : 0 ≤ γ * (f xk - c) / ‖gk‖ ^ 2 := by positivity
  constructor
  · rw [sub_right_comm xk _ y, norm_sub_sq_real, real_inner_smul_right,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hm := mul_le_mul_of_nonneg_left hinner (show 0 ≤ 2 * (γ * (f xk - c) / ‖gk‖ ^ 2) by positivity)
    have heq : ‖xk - y‖ ^ 2 - 2 * (γ * (f xk - c) / ‖gk‖ ^ 2) * (f xk - c) +
        (γ * (f xk - c) / ‖gk‖ ^ 2) ^ 2 * ‖gk‖ ^ 2 =
        ‖xk - y‖ ^ 2 - γ * (2 - γ) * (f xk - c) ^ 2 / ‖gk‖ ^ 2 := by
      field_simp [ne_of_gt (norm_pos_iff.mpr hg)]
      <;> ring
    nlinarith
  · have htwo : 0 < 2 - γ := sub_pos.mpr hγ2
    have hdec : 0 < γ * (2 - γ) * (f xk - c) ^ 2 / ‖gk‖ ^ 2 := by positivity
    linarith
