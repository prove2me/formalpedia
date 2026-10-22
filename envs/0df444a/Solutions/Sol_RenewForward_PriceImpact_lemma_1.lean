-- Prove2me | solution 1 for RenewForward.PriceImpact.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T12:20:40.048991+00:00
-- url     : https://prove2.me/submissions/14408142-71ec-410b-b4d0-094014079a77

import Mathlib
import Definitions.Def_RenewForward_PriceImpact_Setting

open RenewForward.PriceImpact

theorem solution (M : Params) {Ω : Type*} (θ ξ : Ω → ℝ) (kW f1 f2 : ℝ) (w : Ω) (q1 q2 : ℝ) :
    (IsSpotEq M θ ξ kW f1 f2 w q1 q2 ↔
      q1 = spotQ M θ ξ kW f1 f2 w ∧ q2 = spotQ M θ ξ kW f2 f1 w) ∧
    (IsSpotEq M θ ξ kW f1 f2 w q1 q2 →
      spotPrice' M θ ξ kW q1 q2 w = spotP M θ ξ kW (f1 + f2) w) := by
  set D := M.a + θ w - ξ w * kW with hD
  -- the profit gap of a concave quadratic around its maximizer
  have gap : ∀ fi qj q q' : ℝ,
      spotProfit M θ ξ kW fi q' qj w - spotProfit M θ ξ kW fi q qj w
        = (q - (D - qj + fi - M.c) / 2) ^ 2 - (q' - (D - qj + fi - M.c) / 2) ^ 2 := by
    intro fi qj q q'
    simp only [spotProfit, spotPrice', D]; ring
  have fwd : IsSpotEq M θ ξ kW f1 f2 w q1 q2 →
      q1 = spotQ M θ ξ kW f1 f2 w ∧ q2 = spotQ M θ ξ kW f2 f1 w := by
    rintro ⟨h1, h2⟩
    have g1 := h1 ((D - q2 + f1 - M.c) / 2)
    have g2 := h2 ((D - q1 + f2 - M.c) / 2)
    have e1 := gap f1 q2 ((D - q2 + f1 - M.c) / 2) q1
    have e2 := gap f2 q1 ((D - q1 + f2 - M.c) / 2) q2
    have s1 : (q1 - (D - q2 + f1 - M.c) / 2) ^ 2 = 0 := by
      apply le_antisymm _ (sq_nonneg _); nlinarith
    have s2 : (q2 - (D - q1 + f2 - M.c) / 2) ^ 2 = 0 := by
      apply le_antisymm _ (sq_nonneg _); nlinarith
    have t1 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 s1
    have t2 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 s2
    simp only [spotQ, q0]
    constructor <;> linarith
  refine ⟨⟨fwd, ?_⟩, ?_⟩
  · rintro ⟨h1, h2⟩
    simp only [spotQ, q0] at h1 h2
    constructor
    · intro q
      have := gap f1 q2 q q1
      have hq1 : q1 - (D - q2 + f1 - M.c) / 2 = 0 := by rw [h1, h2]; simp only [D]; ring
      rw [hq1] at this
      nlinarith [sq_nonneg (q - (D - q2 + f1 - M.c) / 2)]
    · intro q
      have := gap f2 q1 q q2
      have hq2 : q2 - (D - q1 + f2 - M.c) / 2 = 0 := by rw [h1, h2]; simp only [D]; ring
      rw [hq2] at this
      nlinarith [sq_nonneg (q - (D - q1 + f2 - M.c) / 2)]
  · intro h
    obtain ⟨h1, h2⟩ := fwd h
    rw [h1, h2]
    simp only [spotPrice', spotQ, spotP, q0, p0]
    ring
