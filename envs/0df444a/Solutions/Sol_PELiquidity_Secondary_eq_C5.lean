-- Prove2me | solution 1 for PELiquidity.Secondary.eq_C5
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T18:41:16.697135+00:00
-- url     : https://prove2.me/submissions/0d8eddc6-d854-4aea-9175-71548face3b4

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting

/-- (C.5): minimum L-LP primary-market return. Top-level `solution`
    matching platform target 14007d67-b4da-41e9-a95d-1232f5758d6e. -/
theorem solution (P : PELiquidity.Primary.Params) (D Rb : ℝ)
    (hDlo : 1 - P.δH ≤ D) (hDhi : D ≤ 1 - P.δL) :
    (Rb * (1 - P.lam + P.lam * (1 - D)) = 1 ↔
      Rb = 1 / (1 - P.lam * D)) ∧
    1 / (1 - P.lam * D) = 1 + P.lam * D / (1 - P.lam * D) := by
  obtain ⟨hDpos, hD01⟩ : (0 : ℝ) < D ∧ D < 1 :=
    ⟨by linarith [hDlo, P.hδH1], by linarith [hDhi, P.hδL0]⟩
  have hne : (1 - P.lam * D : ℝ) ≠ 0 := by
    have h1 : P.lam * D ≤ D := by
      have h2 : P.lam * D ≤ (1 : ℝ) * D :=
        mul_le_mul_of_nonneg_right (le_of_lt P.hlam1) (le_of_lt hDpos)
      rw [one_mul] at h2
      exact h2
    exact ne_of_gt (by linarith [h1, hD01])
  constructor
  · rw [show (1 - P.lam + P.lam * (1 - D)) = 1 - P.lam * D by ring, eq_div_iff hne]
  · field_simp
    ring
