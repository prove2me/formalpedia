-- Prove2me | solution 1 for SMHiggsPotential.vacuum_minimizes_potential
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:39:39.324655+00:00
-- url     : https://prove2.me/submissions/fea1821d-4d05-43df-879a-4cb8f1dd84d4

import Mathlib
import Definitions.Def_SMHiggsPotential_Defs

open Complex

open SMHiggsPotential in
theorem solution (g M mh H φ0 : ℝ) (φp : ℂ) :
    scalarLagrangian g M mh 0 H φ0 φp ≤ scalarLagrangian g M mh 0 0 0 0 := by
  unfold scalarLagrangian
  have hkey : 4 * M ^ 2 * alphaH M mh ≤ mh ^ 2 := by
    rcases eq_or_ne M 0 with h | h
    · simp [alphaH, h]; positivity
    · unfold alphaH
      rw [mul_div_cancel₀ _ (by positivity)]
  have ha : 0 ≤ alphaH M mh := by unfold alphaH; positivity
  have hn : 0 ≤ Complex.normSq φp := Complex.normSq_nonneg _
  set a := alphaH M mh
  set n := Complex.normSq φp
  simp only [map_zero]
  have h1 : 0 ≤ a * (4 * M * H + g * (H ^ 2 + φ0 ^ 2 + 2 * n)) ^ 2 :=
    mul_nonneg ha (sq_nonneg _)
  have h2 : 0 ≤ (mh ^ 2 - 4 * M ^ 2 * a) * H ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith [h1, h2]
