-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm_numeric_candidate_combination
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T14:27:02.339822+00:00
-- url     : https://prove2.me/submissions/2ec805d4-a567-408a-bd7e-cde7ad09f0cc

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (β W m f O E : ℝ) (hβ : 0 ≤ β)
    (hupper : O ≤ W + (m + f) / 2) (hforest : f ≤ E)
    (hmatching : (W + 3 * m) / 2 ≤ E) (hproduct : β * (O + W) / 3 ≤ E) :
    11 * β * O ≤ (15 + 5 * β) * E := by
  have hstruct : 6 * O ≤ 5 * W + 5 * E := by linarith
  have h := mul_le_mul_of_nonneg_left hstruct hβ
  nlinarith only [h, hproduct]

#print axioms solution
