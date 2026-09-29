-- Prove2me | solution 1 for Zeta9Note.quadrature_exact_of_moments
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T08:23:58.473666+00:00
-- url     : https://prove2.me/submissions/b8939099-058c-4384-9337-6872cb310ca0

-- Public-mission submission for Zeta9Note.quadrature_exact_of_moments.
-- Statement and proof verified in formalization/Zeta9Note.lean (exit 0, no placeholder).

import Mathlib

open Polynomial

theorem solution
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (y w : Fin 5 → ℝ)
    (hmom : ∀ m : ℕ, m ≤ 4 →
      L ((Polynomial.X : Polynomial ℝ) ^ m) = ∑ j : Fin 5, w j * (y j) ^ m) :
    ∀ p : Polynomial ℝ, p.natDegree ≤ 4 →
      L p = ∑ j : Fin 5, w j * p.eval (y j) := by
  intro p hp
  have h5 : p.natDegree < 5 := by omega
  have hL : L p = ∑ i ∈ Finset.range 5, p.coeff i * L (X ^ i) := by
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' p h5]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Polynomial.smul_eq_C_mul, map_smul]
    rfl
  rw [hL]
  have hR : ∑ j : Fin 5, w j * p.eval (y j) = ∑ i ∈ Finset.range 5, p.coeff i * L (X ^ i) := by
    calc ∑ j : Fin 5, w j * p.eval (y j)
        = ∑ j : Fin 5, ∑ i ∈ Finset.range 5, w j * (p.coeff i * (y j) ^ i) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Polynomial.eval_eq_sum_range' h5, Finset.mul_sum]
      _ = ∑ i ∈ Finset.range 5, ∑ j : Fin 5, w j * (p.coeff i * (y j) ^ i) := by
          rw [Finset.sum_comm]
      _ = ∑ i ∈ Finset.range 5, p.coeff i * ∑ j : Fin 5, w j * (y j) ^ i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i ∈ Finset.range 5, p.coeff i * L (X ^ i) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hmom i (by have := Finset.mem_range.mp hi; omega)]
  exact hR.symm
