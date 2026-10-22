-- Prove2me | solution 1 for QualityEncroach.Uniform.quantity_subgame
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:01:32.880686+00:00
-- url     : https://prove2.me/submissions/52275411-606d-4c3d-80f6-106582415d6d

import Mathlib
import Definitions.Def_QualityEncroach_Uniform_Game

set_option autoImplicit false
open QualityEncroach.Uniform

theorem solution (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (w u : ℝ) (hu : 0 < u) :
    (∀ qR : ℝ, 0 ≤ qR → qR ≤ 1 - c / u - k * u →
        retailerPayoff ⟨w, u, qR, qUM_br k c qR w u⟩ =
          -(1 / 2) * u * qR ^ 2 + ((1 / 2) * u + (1 / 2) * k * u ^ 2 + c / 2 - w) * qR) ∧
    (∀ q : ℝ, -(1 / 2) * u * q ^ 2 + ((1 / 2) * u + (1 / 2) * k * u ^ 2 + c / 2 - w) * q ≤
        -(1 / 2) * u * qUR k c w u ^ 2 +
          ((1 / 2) * u + (1 / 2) * k * u ^ 2 + c / 2 - w) * qUR k c w u) ∧
    (0 ≤ qUR k c w u → qUR k c w u ≤ 1 - c / u - k * u →
        qUM_br k c (qUR k c w u) w u = qUM k c w u ∧
        ∀ qR : ℝ, 0 ≤ qR →
          retailerPayoff ⟨w, u, qR, qUM_br k c qR w u⟩ ≤
            retailerPayoff ⟨w, u, qUR k c w u, qUM k c w u⟩) := by
  have hu' := hu.ne'
  have hcu : c / (2 * u) = c / u / 2 := by ring
  -- (a)
  have ha : ∀ qR : ℝ, 0 ≤ qR → qR ≤ 1 - c / u - k * u →
        retailerPayoff ⟨w, u, qR, qUM_br k c qR w u⟩ =
          -(1 / 2) * u * qR ^ 2 + ((1 / 2) * u + (1 / 2) * k * u ^ 2 + c / 2 - w) * qR := by
    intro qR _ hq
    have h0 : 0 ≤ 1 / 2 - qR / 2 - c / (2 * u) - k * u / 2 := by rw [hcu]; linarith
    unfold qUM_br
    rw [max_eq_right h0]
    simp only [retailerPayoff]
    field_simp
    ring
  -- (b)
  have hb : ∀ q : ℝ, -(1 / 2) * u * q ^ 2 + ((1 / 2) * u + (1 / 2) * k * u ^ 2 + c / 2 - w) * q ≤
        -(1 / 2) * u * qUR k c w u ^ 2 +
          ((1 / 2) * u + (1 / 2) * k * u ^ 2 + c / 2 - w) * qUR k c w u := by
    intro q
    have : (-(1 / 2) * u * qUR k c w u ^ 2 +
          ((1 / 2) * u + (1 / 2) * k * u ^ 2 + c / 2 - w) * qUR k c w u) -
        (-(1 / 2) * u * q ^ 2 + ((1 / 2) * u + (1 / 2) * k * u ^ 2 + c / 2 - w) * q)
        = (u / 2) * (q - qUR k c w u) ^ 2 := by
      unfold qUR
      field_simp
      ring
    nlinarith [mul_nonneg hu.le (sq_nonneg (q - qUR k c w u))]
  refine ⟨ha, hb, ?_⟩
  intro h0 h1
  have hbr : qUM_br k c (qUR k c w u) w u = qUM k c w u := by
    have h0' : 0 ≤ 1 / 2 - qUR k c w u / 2 - c / (2 * u) - k * u / 2 := by
      rw [hcu]; linarith
    unfold qUM_br
    rw [max_eq_right h0']
    unfold qUR qUM
    field_simp
    ring
  refine ⟨hbr, ?_⟩
  intro qR hqR
  have hval : retailerPayoff ⟨w, u, qUR k c w u, qUM k c w u⟩ =
      -(1 / 2) * u * qUR k c w u ^ 2 +
          ((1 / 2) * u + (1 / 2) * k * u ^ 2 + c / 2 - w) * qUR k c w u := by
    rw [← hbr]; exact ha _ h0 h1
  rw [hval]
  rcases le_or_gt qR (1 - c / u - k * u) with hq | hq
  · rw [ha qR hqR hq]; exact hb qR
  · have h0' : 1 / 2 - qR / 2 - c / (2 * u) - k * u / 2 ≤ 0 := by rw [hcu]; linarith
    have hbr0 : qUM_br k c qR w u = 0 := by
      unfold qUM_br; exact max_eq_left h0'
    rw [hbr0]
    have hqq : 0 ≤ qR * (qR - (1 - c / u - k * u)) := mul_nonneg hqR (by linarith)
    have key : retailerPayoff ⟨w, u, qR, 0⟩ =
        (-(1 / 2) * u * qR ^ 2 + ((1 / 2) * u + (1 / 2) * k * u ^ 2 + c / 2 - w) * qR)
          - (u / 2) * (qR * (qR - (1 - c / u - k * u))) := by
      simp only [retailerPayoff]
      field_simp
      ring
    have := hb qR
    nlinarith [mul_nonneg hu.le hqq]
