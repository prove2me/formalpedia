-- Prove2me | solution 1 for RobbinsMonroSA.Conv.eq_42
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:12:37.259506+00:00
-- url     : https://prove2.me/submissions/ef38de6e-41b6-4a42-8289-52f1316371e1

import Mathlib
import Definitions.Def_RobbinsMonroSA_Conv_Setting

set_option autoImplicit false

open Filter Topology

theorem solution (M : ℝ → ℝ) (α θ M' : ℝ) (h33 : Monotone M) (h34 : M θ = α)
    (h35 : HasDerivAt M M' θ) (h35pos : 0 < M') :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : ℝ, δ ≤ A → ∀ z : ℝ, 0 < |z - θ| → |z - θ| ≤ A →
      δ * M' / (2 * A) ≤ (M z - α) / (z - θ) := by
  have hs := hasDerivAt_iff_tendsto_slope.1 h35
  have hev : ∀ᶠ z in 𝓝[≠] θ, M' / 2 < slope M θ z :=
    hs.eventually (lt_mem_nhds (by linarith : M' / 2 < M'))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hεh⟩ := hev
  set e : ℝ := ε / 2 with he
  have he0 : 0 < e := by positivity
  have hkey : ∀ z, z ≠ θ → |z - θ| ≤ e → M' / 2 ≤ (M z - α) / (z - θ) := by
    intro z hz hze
    have h := hεh (y := z) (by rw [Real.dist_eq]; linarith) hz
    rw [slope_def_field, h34] at h
    exact h.le
  refine ⟨e, he0, fun A hA z hz0 hzA => ?_⟩
  have hA0 : 0 < A := lt_of_lt_of_le he0 hA
  have hzne : z ≠ θ := fun h => by rw [h, sub_self, abs_zero] at hz0; exact lt_irrefl _ hz0
  by_cases hsm : |z - θ| ≤ e
  · have h1 := hkey z hzne hsm
    refine le_trans ?_ h1
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · push_neg at hsm
    have hpe := hkey (θ + e) (by intro h; linarith) (by rw [add_sub_cancel_left, abs_of_pos he0])
    have hme := hkey (θ - e) (by intro h; linarith) (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos he0])
    rw [add_sub_cancel_left, le_div_iff₀ he0] at hpe
    have hpe' : e * M' / 2 ≤ M (θ + e) - α := by nlinarith
    rw [show θ - e - θ = -e by ring, div_neg, ← neg_div, neg_sub, le_div_iff₀ he0] at hme
    have hme' : e * M' / 2 ≤ α - M (θ - e) := by nlinarith
    rcases lt_or_gt_of_ne hzne with hlt | hgt
    · -- z < θ
      have hd : e < θ - z := by
        rw [abs_of_neg (by linarith)] at hsm; linarith
      have hmono : M z ≤ M (θ - e) := h33 (by linarith)
      have hdA : θ - z ≤ A := by
        rw [abs_of_neg (by linarith)] at hzA; linarith
      have h1 : e * M' / 2 ≤ α - M z := by linarith
      have eq' : (M z - α) / (z - θ) = (α - M z) / (θ - z) := by
        rw [div_eq_div_iff (sub_ne_zero.2 hzne) (sub_ne_zero.2 hzne.symm)]; ring
      rw [eq', div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 2 * A),
        mul_le_mul_of_nonneg_left hdA (by positivity : (0 : ℝ) ≤ e * M')]
    · have hd : e < z - θ := by
        rw [abs_of_pos (by linarith)] at hsm; linarith
      have hmono : M (θ + e) ≤ M z := h33 (by linarith)
      have hdA : z - θ ≤ A := by
        rw [abs_of_pos (by linarith)] at hzA; linarith
      have h1 : e * M' / 2 ≤ M z - α := by linarith
      rw [div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 2 * A),
        mul_le_mul_of_nonneg_left hdA (by positivity : (0 : ℝ) ≤ e * M')]
