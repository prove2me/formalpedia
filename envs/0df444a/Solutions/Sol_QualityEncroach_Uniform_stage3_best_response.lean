-- Prove2me | solution 1 for QualityEncroach.Uniform.stage3_best_response
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:58:55.466015+00:00
-- url     : https://prove2.me/submissions/b827d273-3404-4301-a19b-a8a9db81052b

import Mathlib
import Definitions.Def_QualityEncroach_Uniform_Game

set_option autoImplicit false
open QualityEncroach.Uniform

theorem solution (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (w u qR : ℝ)
    (hu : 0 < u) (hqR : 0 ≤ qR) :
    0 ≤ qUM_br k c qR w u ∧
    ∀ qM : ℝ, 0 ≤ qM → qM ≠ qUM_br k c qR w u →
      mfrPayoff k c ⟨w, u, qR, qM⟩ < mfrPayoff k c ⟨w, u, qR, qUM_br k c qR w u⟩ := by
  have hu' := hu.ne'
  have key : (1 / 2 - qR / 2 - c / (2 * u) - k * u / 2)
      = (u * (1 - qR) - c - k * u ^ 2) / (2 * u) := by
    field_simp
  unfold qUM_br
  rw [key]
  refine ⟨le_max_left _ _, ?_⟩
  intro qM hqM hne
  simp only [mfrPayoff]
  set d := u * (1 - qR) - c - k * u ^ 2 with hd
  rcases le_total 0 d with h | h
  · rw [max_eq_right (div_nonneg h (by positivity))] at hne ⊢
    set b := d / (2 * u) with hb
    have hb2 : d = 2 * u * b := by rw [hb]; field_simp
    have hne' : 0 < (qM - b) ^ 2 := by
      have : qM - b ≠ 0 := sub_ne_zero.2 hne
      positivity
    have e1 : (u * (1 - qM - qR) - c - k * u ^ 2) = d - u * qM := by rw [hd]; ring
    have e2 : (u * (1 - b - qR) - c - k * u ^ 2) = d - u * b := by rw [hd]; ring
    rw [e1, e2, hb2]
    nlinarith [mul_pos hu hne']
  · have hd0 : d / (2 * u) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h (by positivity)
    rw [max_eq_left hd0] at hne ⊢
    have hq : 0 < qM := lt_of_le_of_ne hqM (Ne.symm hne)
    have e1 : (u * (1 - qM - qR) - c - k * u ^ 2) = d - u * qM := by rw [hd]; ring
    have e2 : (u * (1 - 0 - qR) - c - k * u ^ 2) = d := by rw [hd]; ring
    rw [e1, e2]
    nlinarith [mul_pos hu hq, mul_pos hq hq]
