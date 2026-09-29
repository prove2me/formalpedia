-- Prove2me | solution 1 for Polynomial.exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3dae6cbc-99d0-505e-a88f-e99f6430531b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm

set_option autoImplicit false

open Polynomial

namespace InfLoc

variable {R : Type*} [CommRing R]

noncomputable def rev (n : ℕ) (P : Polynomial (Polynomial R)) (j : ℕ) : Polynomial R :=
  ∑ i ∈ Finset.range (n + 2), C ((P.coeff j).coeff i) * X ^ (n + 1 - i)

theorem eval_zero_rev (n : ℕ) (P : Polynomial (Polynomial R)) (j : ℕ) :
    (rev n P j).eval 0 = (P.coeff j).coeff (n + 1) := by
  unfold rev
  rw [eval_finset_sum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [Finset.sum_eq_single (n + 1)]
  · simp
  · intro i hi hne
    have : n + 1 - i ≠ 0 := by
      have := Finset.mem_range.mp hi; omega
    rw [zero_pow this, mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

variable {A : Type*} [Field A] [Algebra R A]

theorem aeval_inv_rev_mul_pow (n : ℕ) (P : Polynomial (Polynomial R)) (j : ℕ) {x : A} (hx : x ≠ 0) :
    aeval x⁻¹ (rev n P j) * x ^ (n + 1) = ∑ i ∈ Finset.range (n + 2), algebraMap R A ((P.coeff j).coeff i) * x ^ i := by
  unfold rev
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n + 1 := by have := Finset.mem_range.mp hi; omega
  rw [map_mul, aeval_C, map_pow, aeval_X, mul_assoc]
  congr 1
  rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hx, ← zpow_natCast]
  congr 1
  rw [Nat.cast_sub hi']
  push_cast
  ring

theorem eval₂_coeff_eq_sum (n : ℕ) (P : Polynomial (Polynomial R)) (j : ℕ)
    (hvan : ∀ i, n + 1 < i → (P.coeff j).coeff i = 0) (x : A) :
    (P.coeff j).eval₂ (algebraMap R A) x = ∑ i ∈ Finset.range (n + 2), algebraMap R A ((P.coeff j).coeff i) * x ^ i := by
  rw [eval₂_eq_sum, sum_def]
  apply Finset.sum_subset
  · intro i hi
    rw [Finset.mem_range]
    by_contra h
    have := hvan i (by omega)
    exact (mem_support_iff.mp hi) this
  · intro i _ hi
    rw [notMem_support_iff.mp hi, map_zero, zero_mul]

end InfLoc

open InfLoc in

theorem InfLoc.exists_g
    (R : Type*) [CommRing R] (A : Type*) [Field A] [Algebra R A]
    (n : ℕ) (P : Polynomial (Polynomial R)) (hmon : P.Monic) (hdeg : P.natDegree = n + 1)
    (hsym : ∀ i j, (P.coeff i).coeff j = (P.coeff j).coeff i) :
    ∃ g : Polynomial R, g.eval 0 = 1 ∧
      ∀ (x y c : A), x ≠ 0 → y ≠ 0 →
        P.eval₂ (Polynomial.eval₂RingHom (algebraMap R A) x) y = 0 →
        c * Polynomial.aeval x⁻¹ g = 1 →
        IsIntegral (Algebra.adjoin R ({x⁻¹, c} : Set A)) y⁻¹ := by
  classical

  have hlead : P.coeff (n + 1) = 1 := by rw [← hdeg]; exact hmon
  have hvanP : ∀ j, n + 1 < j → P.coeff j = 0 := fun j hj => coeff_eq_zero_of_natDegree_lt (by omega)
  have hvan : ∀ j i, n + 1 < i → (P.coeff j).coeff i = 0 := by
    intro j i hi; rw [← hsym i j, hvanP i hi, coeff_zero]
  refine ⟨rev n P 0, ?_, ?_⟩
  · rw [eval_zero_rev, ← hsym (n + 1) 0, hlead, coeff_one_zero]
  intro x y c hx hy hP hc

  set S := Algebra.adjoin R ({x⁻¹, c} : Set A) with hS
  have hxS : x⁻¹ ∈ S := Algebra.subset_adjoin (by simp)
  have hcS : c ∈ S := Algebra.subset_adjoin (by simp)
  have hrS : ∀ j, aeval x⁻¹ (rev n P j) ∈ S := fun j =>
    (Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (show x⁻¹ ∈ ({x⁻¹, c} : Set A) by simp)))
      (Polynomial.aeval_mem_adjoin_singleton R x⁻¹)

  have hrev : ∑ j ∈ Finset.range (n + 2), aeval x⁻¹ (rev n P j) * y⁻¹ ^ (n + 1 - j) = 0 := by
    have hxn : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hx
    have hyn : y ^ (n + 1) ≠ 0 := pow_ne_zero _ hy
    apply mul_right_cancel₀ hxn
    apply mul_right_cancel₀ hyn
    rw [zero_mul, zero_mul, Finset.sum_mul, Finset.sum_mul]

    have hP' : ∑ j ∈ Finset.range (n + 2), (P.coeff j).eval₂ (algebraMap R A) x * y ^ j = 0 := by
      rw [eval₂_eq_sum, sum_def] at hP
      rw [← hP]
      symm
      apply Finset.sum_subset
      · intro j hj
        rw [Finset.mem_range]
        by_contra h
        exact (mem_support_iff.mp hj) (hvanP j (by omega))
      · intro j _ hj
        rw [notMem_support_iff.mp hj]
        simp
    rw [← hP']
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n + 1 := by have := Finset.mem_range.mp hj; omega
    rw [show aeval x⁻¹ (rev n P j) * y⁻¹ ^ (n + 1 - j) * x ^ (n + 1) * y ^ (n + 1)
        = (aeval x⁻¹ (rev n P j) * x ^ (n + 1)) * (y ^ (n + 1) * y⁻¹ ^ (n + 1 - j)) by ring,
      aeval_inv_rev_mul_pow n P j hx, ← eval₂_coeff_eq_sum n P j (hvan j) x]
    congr 1
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hy, ← zpow_natCast]
    congr 1
    rw [Nat.cast_sub hj']
    push_cast
    ring

  let q : ℕ → S := fun j => ⟨c * aeval x⁻¹ (rev n P j), S.mul_mem hcS (hrS j)⟩
  have hq0 : q 0 = 1 := Subtype.ext (by show c * aeval x⁻¹ (rev n P 0) = 1; exact hc)
  let Q : Polynomial S := X ^ (n + 1) + ∑ j ∈ Finset.Ico 1 (n + 2), C (q j) * X ^ (n + 1 - j)
  have hQdeg : (∑ j ∈ Finset.Ico 1 (n + 2), C (q j) * X ^ (n + 1 - j) : Polynomial S).degree < (n + 1 : ℕ) := by
    refine (degree_sum_le _ _).trans_lt ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun j hj => ?_
    have := Finset.mem_Ico.mp hj
    exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast (show n + 1 - j < n + 1 by omega))
  have hQmon : Q.Monic := by
    show (X ^ (n + 1) + ∑ j ∈ Finset.Ico 1 (n + 2), C (q j) * X ^ (n + 1 - j)).Monic
    exact Monic.add_of_left (monic_X_pow _) (by rwa [degree_X_pow])
  refine ⟨Q, hQmon, ?_⟩

  show eval₂ (algebraMap S A) y⁻¹ (X ^ (n + 1) + ∑ j ∈ Finset.Ico 1 (n + 2), C (q j) * X ^ (n + 1 - j)) = 0
  rw [eval₂_add, eval₂_X_pow, eval₂_finsetSum]
  simp only [eval₂_mul, eval₂_C, eval₂_X_pow]
  have hsplit : ∑ j ∈ Finset.range (n + 2), aeval x⁻¹ (rev n P j) * y⁻¹ ^ (n + 1 - j)
      = aeval x⁻¹ (rev n P 0) * y⁻¹ ^ (n + 1) + ∑ j ∈ Finset.Ico 1 (n + 2), aeval x⁻¹ (rev n P j) * y⁻¹ ^ (n + 1 - j) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < n + 2)]
    simp only [Nat.sub_zero, zero_add]
  have key : c * (∑ j ∈ Finset.range (n + 2), aeval x⁻¹ (rev n P j) * y⁻¹ ^ (n + 1 - j)) = 0 := by rw [hrev, mul_zero]
  rw [hsplit, mul_add, ← mul_assoc, hc, one_mul, Finset.mul_sum] at key
  convert key using 2
  refine Finset.sum_congr rfl fun j _ => ?_
  show (c * aeval x⁻¹ (rev n P j)) * y⁻¹ ^ (n + 1 - j) = c * (aeval x⁻¹ (rev n P j) * y⁻¹ ^ (n + 1 - j))
  ring

theorem solution
    (R : Type*) [CommRing R] (A : Type*) [Field A] [Algebra R A]
    (n : ℕ) (P : Polynomial (Polynomial R)) (hmon : P.Monic) (hdeg : P.natDegree = n + 1)
    (hsym : ∀ i j, (P.coeff i).coeff j = (P.coeff j).coeff i) :
    ∃ h : Polynomial R,
      ∀ (x y c : A), x ≠ 0 → y ≠ 0 →
        P.eval₂ (Polynomial.eval₂RingHom (algebraMap R A) x) y = 0 →
        c * (1 + x⁻¹ * Polynomial.aeval x⁻¹ h) = 1 →
        IsIntegral (Algebra.adjoin R ({x⁻¹, c} : Set A)) y⁻¹ := by
  obtain ⟨g, hg0, hg⟩ := InfLoc.exists_g R A n P hmon hdeg hsym
  refine ⟨g.divX, fun x y c hx hy hP hc => hg x y c hx hy hP ?_⟩
  have hsplit : g = X * g.divX + C (g.coeff 0) := (X_mul_divX_add g).symm
  rw [coeff_zero_eq_eval_zero, hg0, map_one] at hsplit
  rw [hsplit, map_add, map_mul, aeval_X, map_one, add_comm]
  exact hc

end S_Polynomial_exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm
end P2MW
export P2MW.S_Polynomial_exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm (solution)
