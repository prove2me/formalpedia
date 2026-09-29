-- Prove2me | solution 1 for Pade.pade_linearization_iff_series
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T08:51:32.031532+00:00
-- url     : https://prove2.me/submissions/a679fb04-d1db-4dcc-b070-222a0e0d9d9f

import Mathlib
import Definitions.Def_pade_approximant_def
open Polynomial

open Pade

theorem solution {F : Type*} [Field F] (f : PowerSeries F) (m n : ℕ)
    (P Q : Polynomial F) (hQ : Q.coeff 0 ≠ 0) :
    (∀ k ≤ m + n, PowerSeries.coeff k ((Q : PowerSeries F) * f - (P : PowerSeries F)) = 0) ↔
      (∀ k ≤ m + n,
        PowerSeries.coeff k (f - (P : PowerSeries F) * ((Q : PowerSeries F))⁻¹) = 0) := by
  have hc : PowerSeries.constantCoeff (Q : PowerSeries F) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]; exact hQ
  have hinv : (Q : PowerSeries F) * (Q : PowerSeries F)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hc
  have e1 : f - (P : PowerSeries F) * ((Q : PowerSeries F))⁻¹ =
      ((Q : PowerSeries F))⁻¹ * ((Q : PowerSeries F) * f - P) := by
    linear_combination (-f) * hinv
  have e2 : (Q : PowerSeries F) * f - P =
      (Q : PowerSeries F) * (f - (P : PowerSeries F) * ((Q : PowerSeries F))⁻¹) := by
    linear_combination (P : PowerSeries F) * hinv
  have key : ∀ g : PowerSeries F, (∀ k ≤ m + n, PowerSeries.coeff k g = 0) ↔
      (PowerSeries.X : PowerSeries F) ^ (m + n + 1) ∣ g := by
    intro g
    rw [PowerSeries.X_pow_dvd_iff]
    exact ⟨fun h j hj => h j (by omega), fun h j hj => h j (by omega)⟩
  rw [key, key]
  constructor
  · intro h; rw [e1]; exact dvd_mul_of_dvd_right h _
  · intro h; rw [e2]; exact dvd_mul_of_dvd_right h _
