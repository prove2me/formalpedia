-- Prove2me | solution 1 for PolyhedralSOC.UpperBound.planar_approx_quality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T06:17:44.974257+00:00
-- url     : https://prove2.me/submissions/388890c3-77fc-48e7-ab0f-45fefded2f38

import Mathlib
import Definitions.Def_PolyhedralSOC_UpperBound_System8

open PolyhedralSOC.UpperBound

private theorem theta_le (j : ℕ) (hj : 1 ≤ j) : Real.pi / 2 ^ (j + 1) ≤ Real.pi / 4 := by
  have hpi := Real.pi_pos
  have h4 : (4:ℝ) ≤ 2 ^ (j + 1) := by
    have h2 : (2:ℝ) ^ 2 ≤ 2 ^ (j + 1) := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    norm_num at h2
    exact h2
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [hpi, h4]

private theorem theta_pos (j : ℕ) : 0 < Real.pi / 2 ^ (j + 1) := by
  have := Real.pi_pos; positivity

private theorem cos_pos_theta (j : ℕ) (hj : 1 ≤ j) : 0 < Real.cos (Real.pi / 2 ^ (j + 1)) := by
  have hpi := Real.pi_pos
  refine Real.cos_pos_of_mem_Ioo ⟨by linarith [theta_pos j], ?_⟩
  have h := theta_le j hj
  linarith

private theorem sin_nonneg_theta (j : ℕ) : 0 ≤ Real.sin (Real.pi / 2 ^ (j + 1)) := by
  have hpi := Real.pi_pos
  refine Real.sin_nonneg_of_nonneg_of_le_pi (theta_pos j).le ?_
  have hpow : (1:ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hpi]

theorem solution (ν : ℕ) (hν : 1 ≤ ν) (x₁ x₂ x₃ : ℝ) (ξ η : ℕ → ℝ)
    (h : System8 ν x₁ x₂ x₃ ξ η) :
    Real.sqrt (x₁ ^ 2 + x₂ ^ 2) ≤ (1 + delta ν) * x₃ := by
  obtain ⟨⟨h0ξ, h0η⟩, hrec, hfin1, hfin2⟩ := h
  -- the rotation invariant
  have key : ∀ j : ℕ, j ≤ ν → 0 ≤ ξ j ∧ 0 ≤ η j ∧ ξ 0 ^ 2 + η 0 ^ 2 ≤ ξ j ^ 2 + η j ^ 2 := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨le_trans (abs_nonneg x₁) h0ξ, le_trans (abs_nonneg x₂) h0η, le_refl _⟩
    | succ m ih =>
      intro hm
      obtain ⟨hξm, hηm, hinv⟩ := ih (by omega)
      obtain ⟨heq, hge⟩ := hrec (m + 1) (by omega) hm
      simp only [Nat.add_sub_cancel] at heq hge
      have hc := cos_pos_theta (m + 1) (by omega)
      have hs := sin_nonneg_theta (m + 1)
      have hpy : Real.sin (Real.pi / 2 ^ (m + 1 + 1)) ^ 2
          + Real.cos (Real.pi / 2 ^ (m + 1 + 1)) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
      refine ⟨by rw [heq]; positivity, le_trans (abs_nonneg _) hge, ?_⟩
      have hsq : (-Real.sin (Real.pi / 2 ^ (m + 1 + 1)) * ξ m
          + Real.cos (Real.pi / 2 ^ (m + 1 + 1)) * η m) ^ 2 ≤ η (m + 1) ^ 2 := by
        have habs := hge
        have h1 : |(-Real.sin (Real.pi / 2 ^ (m + 1 + 1)) * ξ m
            + Real.cos (Real.pi / 2 ^ (m + 1 + 1)) * η m)| ≤ η (m + 1) := hge
        nlinarith [abs_nonneg (-Real.sin (Real.pi / 2 ^ (m + 1 + 1)) * ξ m
            + Real.cos (Real.pi / 2 ^ (m + 1 + 1)) * η m),
          sq_abs (-Real.sin (Real.pi / 2 ^ (m + 1 + 1)) * ξ m
            + Real.cos (Real.pi / 2 ^ (m + 1 + 1)) * η m)]
      have hrot : ξ (m + 1) ^ 2
          + (-Real.sin (Real.pi / 2 ^ (m + 1 + 1)) * ξ m
            + Real.cos (Real.pi / 2 ^ (m + 1 + 1)) * η m) ^ 2 = ξ m ^ 2 + η m ^ 2 := by
        rw [heq]
        nlinarith [hpy]
      linarith
  obtain ⟨hξν, hην, hinvν⟩ := key ν (le_refl ν)
  have hc := cos_pos_theta ν hν
  have hs := sin_nonneg_theta ν
  have hpy : Real.sin (Real.pi / 2 ^ (ν + 1)) ^ 2 + Real.cos (Real.pi / 2 ^ (ν + 1)) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  -- the endgame: `ξ ν² + η ν² ≤ (ξ ν / cos θ)²`
  have htan : Real.tan (Real.pi / 2 ^ (ν + 1))
      = Real.sin (Real.pi / 2 ^ (ν + 1)) / Real.cos (Real.pi / 2 ^ (ν + 1)) :=
    Real.tan_eq_sin_div_cos _
  have hbound : ξ ν ^ 2 + η ν ^ 2 ≤ (ξ ν / Real.cos (Real.pi / 2 ^ (ν + 1))) ^ 2 := by
    rw [htan] at hfin2
    have hη2 : η ν ^ 2
        ≤ (Real.sin (Real.pi / 2 ^ (ν + 1)) / Real.cos (Real.pi / 2 ^ (ν + 1))) ^ 2 * ξ ν ^ 2 := by
      have hnn : 0 ≤ Real.sin (Real.pi / 2 ^ (ν + 1)) / Real.cos (Real.pi / 2 ^ (ν + 1)) :=
        div_nonneg hs hc.le
      nlinarith [hfin2, hην, hξν, mul_nonneg hnn hξν]
    rw [div_pow] at hη2
    have hc2 : (0:ℝ) < Real.cos (Real.pi / 2 ^ (ν + 1)) ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hc2] at hη2
    rw [div_pow, le_div_iff₀ hc2]
    have hid : ξ ν ^ 2 * (Real.sin (Real.pi / 2 ^ (ν + 1)) ^ 2
        + Real.cos (Real.pi / 2 ^ (ν + 1)) ^ 2) = ξ ν ^ 2 := by rw [hpy]; ring
    nlinarith [hη2, hid]
  -- conclude
  have hx : x₁ ^ 2 + x₂ ^ 2 ≤ ξ 0 ^ 2 + η 0 ^ 2 := by
    have h1 : x₁ ^ 2 ≤ ξ 0 ^ 2 := by
      nlinarith [abs_nonneg x₁, h0ξ, sq_abs x₁]
    have h2 : x₂ ^ 2 ≤ η 0 ^ 2 := by
      nlinarith [abs_nonneg x₂, h0η, sq_abs x₂]
    linarith
  have hratio : 0 ≤ ξ ν / Real.cos (Real.pi / 2 ^ (ν + 1)) := div_nonneg hξν hc.le
  have hsq : Real.sqrt (x₁ ^ 2 + x₂ ^ 2) ≤ ξ ν / Real.cos (Real.pi / 2 ^ (ν + 1)) := by
    have hle : x₁ ^ 2 + x₂ ^ 2 ≤ (ξ ν / Real.cos (Real.pi / 2 ^ (ν + 1))) ^ 2 := by linarith
    calc Real.sqrt (x₁ ^ 2 + x₂ ^ 2)
        ≤ Real.sqrt ((ξ ν / Real.cos (Real.pi / 2 ^ (ν + 1))) ^ 2) := Real.sqrt_le_sqrt hle
      _ = ξ ν / Real.cos (Real.pi / 2 ^ (ν + 1)) := Real.sqrt_sq hratio
  have hdel : 1 + delta ν = 1 / Real.cos (Real.pi / 2 ^ (ν + 1)) := by
    rw [delta]; ring
  rw [hdel]
  have hxi3 : ξ ν ≤ x₃ := hfin1
  calc Real.sqrt (x₁ ^ 2 + x₂ ^ 2) ≤ ξ ν / Real.cos (Real.pi / 2 ^ (ν + 1)) := hsq
    _ = (1 / Real.cos (Real.pi / 2 ^ (ν + 1))) * ξ ν := by ring
    _ ≤ (1 / Real.cos (Real.pi / 2 ^ (ν + 1))) * x₃ := by
        apply mul_le_mul_of_nonneg_left hxi3 (by positivity)
