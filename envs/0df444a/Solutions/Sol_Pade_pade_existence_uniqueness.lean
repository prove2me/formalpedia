-- Prove2me | solution 1 for Pade.pade_existence_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T08:44:09.063039+00:00
-- url     : https://prove2.me/submissions/7be7135e-4fa2-4102-afd7-8d8ce1137732

import Mathlib
import Definitions.Def_pade_approximant_def
open Polynomial

open Pade

namespace Ag1Aux_PadeEU

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

theorem exists_core {F : Type*} [Field F] (f : PowerSeries F) (m n : ℕ) :
    ∃ P Q : Polynomial F, IsPadeApproximant f m n P Q := by
  classical
  let A : Matrix (Fin n) (Fin (n + 1)) F := fun i j =>
    PowerSeries.coeff (m + 1 + (i : ℕ)) ((PowerSeries.X : PowerSeries F) ^ (j : ℕ) * f)
  have hker : LinearMap.ker (Matrix.mulVecLin A) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hc
  set Q : Polynomial F := ∑ j : Fin (n + 1), C (c j) * X ^ (j : ℕ) with hQ
  have hQcoeff : ∀ j : Fin (n + 1), Q.coeff j = c j := by
    intro j
    rw [hQ, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h; exact hb (Fin.ext h.symm)
    · simp
  have hQdeg : Q.degree ≤ (n : WithBot ℕ) := by
    have := degree_sum_fin_lt (n := n + 1) c
    rw [hQ]
    refine (degree_le_iff_coeff_zero _ _).2 (fun k hk => coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le this ?_))
    have hk' : n < k := by exact_mod_cast hk
    exact_mod_cast (by omega : n + 1 ≤ k)
  have hQcoe : (Q : PowerSeries F) =
      ∑ j : Fin (n + 1), PowerSeries.C (c j) * (PowerSeries.X : PowerSeries F) ^ (j : ℕ) := by
    rw [hQ, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp [Polynomial.coeToPowerSeries.ringHom_apply]
  refine ⟨PowerSeries.trunc (m + 1) ((Q : PowerSeries F) * f), Q, ?_, ?_, hQdeg, ?_⟩
  · intro h0
    apply hc0
    funext j
    rw [← hQcoeff j, h0]; simp
  · refine (degree_le_iff_coeff_zero _ _).2 ?_
    intro k hk
    rw [PowerSeries.coeff_trunc, if_neg]
    have : m < k := by exact_mod_cast hk
    omega
  · intro k hk
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with h
    · simp
    · simp only [sub_zero]
      have hi : k - (m + 1) < n := by omega
      have := congrFun hc ⟨k - (m + 1), hi⟩
      simp only [Matrix.mulVec, dotProduct, A, Pi.zero_apply] at this
      rw [hQcoe, Finset.sum_mul, map_sum]
      rw [← this]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_assoc, PowerSeries.coeff_C_mul, mul_comm]
      congr 3
      omega

end Ag1Aux_PadeEU

theorem solution {F : Type*} [Field F] (f : PowerSeries F) (m n : ℕ) :
    (∃ P Q : Polynomial F, IsPadeApproximant f m n P Q) ∧
      (∀ P₁ Q₁ P₂ Q₂ : Polynomial F, IsPadeApproximant f m n P₁ Q₁ →
        IsPadeApproximant f m n P₂ Q₂ → P₁ * Q₂ = P₂ * Q₁) :=
  ⟨Ag1Aux_PadeEU.exists_core f m n, fun P₁ Q₁ P₂ Q₂ h₁ h₂ =>
    Ag1Aux_PadeEU.unique_core f m n P₁ Q₁ P₂ Q₂ h₁ h₂⟩
