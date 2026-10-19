-- Prove2me | solution 1 for PereiraGuimaraesElko.appendix_A_gives_eqs_2_2_to_2_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:15:33.642833+00:00
-- url     : https://prove2.me/submissions/698643b1-5e2f-44f4-b36b-b81b24f7f8d7

import Mathlib

theorem solution (κ : ℝ) (H h f Φ V : ℝ → ℝ) (t : ℝ)
    (hA14 : 3 * H t ^ 2 = κ ^ 2 * (deriv Φ t ^ 2 / 2 + V (Φ t) + 3 / 8 * H t ^ 2 * Φ t ^ 2
          + 3 / 4 * H t * h t * Φ t ^ 2)
        + 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * h t ^ 2
        + 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * f t ^ 2)
    (hA15 : -2 * deriv H t - 3 * H t ^ 2 = κ ^ 2 * (deriv Φ t ^ 2 / 2 - V (Φ t)
          - 3 / 8 * H t ^ 2 * Φ t ^ 2 - 1 / 4 * deriv (fun s => (H s + h s) * Φ s ^ 2) t)
        + 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * h t ^ 2
        - 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * f t ^ 2)
    (hA16 : deriv (deriv Φ) t + 3 * H t * deriv Φ t + deriv V (Φ t)
        - 3 / 4 * ((H t + h t) ^ 2 - f t ^ 2) * Φ t = 0)
    (hf : f t = 0) :
    H t ^ 2 = κ ^ 2 / 3 * (deriv Φ t ^ 2 / 2 + V (Φ t)
        + 3 / 8 * H t ^ 2 * Φ t ^ 2 + 3 / 4 * H t * h t * Φ t ^ 2)
        + (1 + κ ^ 2 * Φ t ^ 2 / 8) * h t ^ 2 ∧
    deriv H t = -(κ ^ 2 / 2) * (deriv Φ t ^ 2 + 3 / 4 * H t * h t * Φ t ^ 2
        - 1 / 4 * deriv (fun s => (H s + h s) * Φ s ^ 2) t)
        - 3 * (1 + κ ^ 2 * Φ t ^ 2 / 8) * h t ^ 2 ∧
    deriv (deriv Φ) t + 3 * H t * deriv Φ t + deriv V (Φ t)
        - 3 / 4 * (H t + h t) ^ 2 * Φ t = 0 := by
  rw [hf] at hA14 hA15 hA16
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (1 / 3 : ℝ) * hA14
  · linear_combination (-(1 / 2) : ℝ) * hA15 - (1 / 2 : ℝ) * hA14
  · linear_combination hA16
