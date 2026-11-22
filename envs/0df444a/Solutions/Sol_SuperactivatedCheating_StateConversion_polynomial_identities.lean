-- Prove2me | solution 1 for SuperactivatedCheating.StateConversion.polynomial_identities
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T05:23:35.012783+00:00
-- url     : https://prove2.me/submissions/4a39b117-5200-450e-bc2e-2d1b59522f48

import Mathlib
import Definitions.Def_SuperactivatedCheating_StateConversion_GameSC

open Polynomial
open SuperactivatedCheating.StateConversion

theorem solution :
    polyP = 1 + 2 * X + 3 * X ^ 2 + X ^ 3 + X ^ 4 + 3 * X ^ 5 + X ^ 6 ∧
    (∃ i, polyS.coeff i < 0) ∧
    polyS ^ 2 = 1 + 2 * X + 5 * X ^ 2 + 2 * X ^ 3 + 6 * X ^ 4 + 2 * X ^ 5 + 11 * X ^ 6 +
      2 * X ^ 8 + 4 * X ^ 9 + X ^ 10 ∧
    polyS ^ 3 = 1 + 3 * X + 9 * X ^ 2 + 10 * X ^ 3 + 18 * X ^ 4 + 12 * X ^ 5 + 35 * X ^ 6 +
      18 * X ^ 7 + 36 * X ^ 8 + 5 * X ^ 9 + 33 * X ^ 10 + 18 * X ^ 11 + 2 * X ^ 12 +
      9 * X ^ 13 + 6 * X ^ 14 + X ^ 15 ∧
    (∀ i, 0 ≤ (polyS ^ 2).coeff i) ∧ (∀ i, 0 ≤ (polyS ^ 3).coeff i) := by
  have nn (p : ℕ[X]) (q : ℤ[X]) (h : p.map (Nat.castRingHom ℤ) = q) (i : ℕ) :
      0 ≤ q.coeff i := by
    rw [← h, Polynomial.coeff_map]
    exact Int.natCast_nonneg _
  refine ⟨?_, ⟨3, ?_⟩, ?_, ?_, ?_, ?_⟩
  · unfold polyP polyS
    ring
  · norm_num [polyS, coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_pow, coeff_one, coeff_X]
  · unfold polyS
    ring
  · unfold polyS
    ring
  · apply nn (1 + 2 * X + 5 * X ^ 2 + 2 * X ^ 3 + 6 * X ^ 4 + 2 * X ^ 5 + 11 * X ^ 6 +
        2 * X ^ 8 + 4 * X ^ 9 + X ^ 10)
    simp [polyS]
    ring
  · apply nn (1 + 3 * X + 9 * X ^ 2 + 10 * X ^ 3 + 18 * X ^ 4 + 12 * X ^ 5 + 35 * X ^ 6 +
        18 * X ^ 7 + 36 * X ^ 8 + 5 * X ^ 9 + 33 * X ^ 10 + 18 * X ^ 11 + 2 * X ^ 12 +
        9 * X ^ 13 + 6 * X ^ 14 + X ^ 15)
    simp [polyS]
    ring
