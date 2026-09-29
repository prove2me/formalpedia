-- Prove2me | solution 1 for Pade.pade_unique
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T08:44:09.013676+00:00
-- url     : https://prove2.me/submissions/7c442f5c-4639-493b-9662-ce034d82715c

import Mathlib
import Definitions.Def_pade_approximant_def
open Polynomial

open Pade

namespace Ag1Aux_PadeUnique

theorem unique_core {F : Type*} [Field F] (f : PowerSeries F) (m n : ℕ)
    (P₁ Q₁ P₂ Q₂ : Polynomial F) (h₁ : IsPadeApproximant f m n P₁ Q₁)
    (h₂ : IsPadeApproximant f m n P₂ Q₂) : P₁ * Q₂ = P₂ * Q₁ := by
  obtain ⟨-, hP1, hQ1, h1⟩ := h₁
  obtain ⟨-, hP2, hQ2, h2⟩ := h₂
  rw [← sub_eq_zero]
  set D := P₁ * Q₂ - P₂ * Q₁ with hD
  have hdeg : D.degree ≤ ((m + n : ℕ) : WithBot ℕ) := by
    refine (degree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (degree_mul_le _ _).trans ?_
      calc P₁.degree + Q₂.degree ≤ (m : WithBot ℕ) + (n : WithBot ℕ) := add_le_add hP1 hQ2
        _ = _ := by push_cast; rfl
    · refine (degree_mul_le _ _).trans ?_
      calc P₂.degree + Q₁.degree ≤ (m : WithBot ℕ) + (n : WithBot ℕ) := add_le_add hP2 hQ1
        _ = _ := by push_cast; rfl
  have hcoe : (D : PowerSeries F) = (Q₁ : PowerSeries F) * ((Q₂ : PowerSeries F) * f - P₂)
      - (Q₂ : PowerSeries F) * ((Q₁ : PowerSeries F) * f - P₁) := by
    rw [hD]; push_cast; ring
  have a1 : (PowerSeries.X : PowerSeries F) ^ (m + n + 1) ∣ (Q₁ : PowerSeries F) * f - P₁ :=
    PowerSeries.X_pow_dvd_iff.2 (fun j hj => h1 j (by omega))
  have a2 : (PowerSeries.X : PowerSeries F) ^ (m + n + 1) ∣ (Q₂ : PowerSeries F) * f - P₂ :=
    PowerSeries.X_pow_dvd_iff.2 (fun j hj => h2 j (by omega))
  have a3 : (PowerSeries.X : PowerSeries F) ^ (m + n + 1) ∣ (D : PowerSeries F) := by
    rw [hcoe]; exact dvd_sub (dvd_mul_of_dvd_right a2 _) (dvd_mul_of_dvd_right a1 _)
  ext k
  rw [coeff_zero]
  by_cases hk : k ≤ m + n
  · rw [← Polynomial.coeff_coe]
    exact PowerSeries.X_pow_dvd_iff.1 a3 k (by omega)
  · exact coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hdeg (by exact_mod_cast (by omega : m + n < k)))

end Ag1Aux_PadeUnique

theorem solution {F : Type*} [Field F] (f : PowerSeries F) (m n : ℕ)
    (P₁ Q₁ P₂ Q₂ : Polynomial F) (h₁ : IsPadeApproximant f m n P₁ Q₁)
    (h₂ : IsPadeApproximant f m n P₂ Q₂) : P₁ * Q₂ = P₂ * Q₁ :=
  Ag1Aux_PadeUnique.unique_core f m n P₁ Q₁ P₂ Q₂ h₁ h₂
