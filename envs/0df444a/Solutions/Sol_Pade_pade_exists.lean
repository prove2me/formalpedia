-- Prove2me | solution 1 for Pade.pade_exists
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T08:44:09.158027+00:00
-- url     : https://prove2.me/submissions/95820b50-a42c-4e6b-8f7d-f5891b95e0ef

import Mathlib
import Definitions.Def_pade_approximant_def
open Polynomial

open Pade

namespace Ag1Aux_PadeExists

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

end Ag1Aux_PadeExists

theorem solution {F : Type*} [Field F] (f : PowerSeries F) (m n : ℕ) :
    ∃ P Q : Polynomial F, IsPadeApproximant f m n P Q :=
  Ag1Aux_PadeExists.exists_core f m n
