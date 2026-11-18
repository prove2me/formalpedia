-- Prove2me | solution 1 for RealPinwheel.FiveSixths.D5_region_0001
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:44:58.45671+00:00
-- url     : https://prove2.me/submissions/1cd15230-76ed-4f62-b7ee-e15a347a2db4

import Theorems.Thm_RealPinwheel_FiveSixths_density_certificate_5
open RealPinwheel.FiveSixths
theorem solution (A : Instance 5) (hD : density A ≤ (5 : ℝ) / 6)
    (r0 : ¬ (1 / A.period 0 ≤ (3 : ℝ) / 14))
    (r1 : 1 / A.period 0 ≤ (5 : ℝ) / 14)
    : ∃ (L : ℕ) (S : ℕ → Fin 5), 0 < L ∧ L ≤ 32 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S  := by
  exact density_certificate_5 A hD
