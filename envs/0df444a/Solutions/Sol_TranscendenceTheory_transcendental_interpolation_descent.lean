-- Prove2me | solution 1 for TranscendenceTheory.transcendental_interpolation_descent
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-19T16:31:43.826676+00:00
-- url     : https://prove2.me/submissions/b0b4312f-634e-4a0e-b696-f235306333b4

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Choose

open scoped BigOperators
open Polynomial

private theorem linear_system_descent
    (K L ι α : Type*) [Field K] [CommRing L] [Algebra K L] [Fintype ι]
    (φ : Polynomial K →ₐ[K] L) (hφ : Function.Injective φ)
    (b : ℕ) (A : α → ι → K) (B : α → Polynomial K)
    (hB : ∀ a, (B a).natDegree ≤ b) :
    (∃ w : ι → L, ∀ a, ∑ i, algebraMap K L (A a i) * w i = φ (B a)) ↔
      ∀ k ≤ b, ∃ u : ι → K, ∀ a, ∑ i, A a i * u i = (B a).coeff k := by
  classical
  constructor
  · obtain ⟨r, hr⟩ := φ.toLinearMap.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr hφ)
    have hr' (p : Polynomial K) : r (φ p) = p :=
      DFunLike.congr_fun hr p
    rintro ⟨w, hw⟩ k hk
    let μ : L →ₗ[K] K := (Polynomial.lcoeff K k).comp r
    refine ⟨fun i => μ (w i), ?_⟩
    intro a
    have h := congrArg μ (hw a)
    have hμ (c : K) (x : L) : μ (algebraMap K L c * x) = c * μ x := by
      simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply] using μ.map_smul c x
    simpa only [map_sum, hμ, μ, LinearMap.comp_apply, Polynomial.lcoeff_apply,
      hr'] using h
  · intro h
    choose u hu using fun k : Fin (b + 1) => h k.val (by omega)
    let W : ι → Polynomial K := fun i =>
      ∑ k : Fin (b + 1), Polynomial.monomial k.val (u k i)
    have hW (i : ι) (k : Fin (b + 1)) : (W i).coeff k.val = u k i := by
      simp only [W, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Fin.val_inj]
      simp
    have hWzero (i : ι) (k : ℕ) (hk : b < k) : (W i).coeff k = 0 := by
      simp only [W, Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Polynomial.coeff_monomial]
      split_ifs with he
      · omega
      · rfl
    have hpoly (a : α) : ∑ i, (A a i) • W i = B a := by
      ext k
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul]
      by_cases hk : k ≤ b
      · have hc (i : ι) : (W i).coeff k = u ⟨k, by omega⟩ i := hW i ⟨k, by omega⟩
        simp only [hc]
        exact hu ⟨k, by omega⟩ a
      · simp only [hWzero _ k (Nat.lt_of_not_ge hk), mul_zero, Finset.sum_const_zero]
        exact (Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (hB a) (Nat.lt_of_not_ge hk))).symm
    refine ⟨fun i => φ (W i), ?_⟩
    intro a
    have h := congrArg φ (hpoly a)
    simpa only [map_sum, Algebra.smul_def, map_mul, AlgHom.commutes] using h

theorem solution
    (K L ι : Type*) [Field K] [CommRing L] [Algebra K L] [Fintype ι]
    (φ : Polynomial K →ₐ[K] L) (hφ : Function.Injective φ)
    (b : ℕ) (c : K) (V : ι → ℕ → Polynomial K) (Q : Polynomial K) :
    (∃ w : ι → L, ∀ j ≤ b,
      (1 - Polynomial.C (algebraMap K L c) * Polynomial.X) *
        (∑ i, Polynomial.C (w i) * (V i j).map (algebraMap K L)) =
          Polynomial.C ((φ Polynomial.X) ^ j) * Q.map (algebraMap K L)) ↔
    (∀ k ≤ b, ∃ u : ι → K, ∀ j ≤ b,
      (1 - Polynomial.C c * Polynomial.X) *
        (∑ i, Polynomial.C (u i) * V i j) = if k = j then Q else 0) := by
  classical
  let A : (Fin (b + 1) × ℕ) → ι → K := fun a i =>
    ((1 - Polynomial.C c * Polynomial.X) * V i a.1.val).coeff a.2
  let B : (Fin (b + 1) × ℕ) → Polynomial K := fun a =>
    Polynomial.C (Q.coeff a.2) * Polynomial.X ^ a.1.val
  have hB (a : Fin (b + 1) × ℕ) : (B a).natDegree ≤ b := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.natDegree_X_pow_le _).trans (by omega))
  have hcoeff (w : ι → L) (j : ℕ) (n : ℕ) :
      ((1 - Polynomial.C (algebraMap K L c) * Polynomial.X) *
        (∑ i, Polynomial.C (w i) * (V i j).map (algebraMap K L))).coeff n =
      ∑ i, algebraMap K L
        (((1 - Polynomial.C c * Polynomial.X) * V i j).coeff n) * w i := by
    rw [Finset.mul_sum]
    simp only [Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro i hi
    have he : (1 - Polynomial.C (algebraMap K L c) * Polynomial.X) *
        (Polynomial.C (w i) * (V i j).map (algebraMap K L)) =
        Polynomial.C (w i) *
          (((1 - Polynomial.C c * Polynomial.X) * V i j).map (algebraMap K L)) := by
      simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
        Polynomial.map_C, Polynomial.map_X]
      ring
    rw [he, Polynomial.coeff_C_mul, Polynomial.coeff_map]
    exact mul_comm _ _
  have hcoeffK (u : ι → K) (j : ℕ) (n : ℕ) :
      ((1 - Polynomial.C c * Polynomial.X) *
        (∑ i, Polynomial.C (u i) * V i j)).coeff n =
      ∑ i, (((1 - Polynomial.C c * Polynomial.X) * V i j).coeff n) * u i := by
    rw [Finset.mul_sum]
    simp only [Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (1 - Polynomial.C c * Polynomial.X) * (Polynomial.C (u i) * V i j) =
      Polynomial.C (u i) * ((1 - Polynomial.C c * Polynomial.X) * V i j) by ring]
    rw [Polynomial.coeff_C_mul]
    exact mul_comm _ _
  have hleft :
      (∃ w : ι → L, ∀ j ≤ b,
        (1 - Polynomial.C (algebraMap K L c) * Polynomial.X) *
          (∑ i, Polynomial.C (w i) * (V i j).map (algebraMap K L)) =
            Polynomial.C ((φ Polynomial.X) ^ j) * Q.map (algebraMap K L)) ↔
      (∃ w : ι → L, ∀ a, ∑ i, algebraMap K L (A a i) * w i = φ (B a)) := by
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨w, ?_⟩
      intro a
      have he := congrArg (fun p : Polynomial L => p.coeff a.2)
        (hw a.1.val (by omega))
      rw [hcoeff, Polynomial.coeff_C_mul, Polynomial.coeff_map] at he
      simpa only [A, B, map_mul, map_pow, Polynomial.C_eq_algebraMap,
        AlgHom.commutes, mul_comm] using he
    · rintro ⟨w, hw⟩
      refine ⟨w, ?_⟩
      intro j hj
      ext n
      rw [hcoeff, Polynomial.coeff_C_mul, Polynomial.coeff_map]
      simpa only [A, B, map_mul, map_pow, Polynomial.C_eq_algebraMap,
        AlgHom.commutes, mul_comm] using hw (⟨j, by omega⟩, n)
  rw [hleft, linear_system_descent K L ι _ φ hφ b A B hB]
  apply forall₂_congr
  intro k hk
  apply exists_congr
  intro u
  constructor
  · intro hu j hj
    ext n
    have he := hu (⟨j, by omega⟩, n)
    simpa [A, B, hcoeffK, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      apply_ite (fun p : Polynomial K => p.coeff n), eq_comm] using he
  · intro hu a
    have he := congrArg (fun p : Polynomial K => p.coeff a.2)
      (hu a.1.val (by omega))
    simpa [A, B, hcoeffK, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      apply_ite (fun p : Polynomial K => p.coeff a.2), eq_comm] using he
