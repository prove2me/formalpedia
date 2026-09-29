-- Prove2me | solution 1 for Polynomial.natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/acc15f1f-d380-5289-916f-1ff135832de3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial

theorem solution
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (c : Polynomial L) (n : ℕ)
    (h : Polynomial.aeval x c * (x ^ n)⁻¹ ∈ Algebra.adjoin L ({x⁻¹} : Set F)) :
    c.natDegree ≤ n := by
  classical
  by_cases hc0 : c = 0
  · simp [hc0]

  rw [Algebra.adjoin_singleton_eq_range_aeval L x⁻¹, AlgHom.mem_range] at h
  obtain ⟨p, hp⟩ := h
  set N : ℕ := max n p.natDegree with hN
  have hnN : n ≤ N := le_max_left _ _
  have hpN : p.natDegree ≤ N := le_max_right _ _

  haveI : Invertible (x⁻¹) := invertibleOfNonzero (inv_ne_zero hx0)
  have hxinvinv : ⅟(x⁻¹) = x := by rw [invOf_eq_inv, inv_inv]
  have hrefl : Polynomial.aeval x (p.reflect N) * (x⁻¹) ^ N = Polynomial.aeval x⁻¹ p := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def]
    have := Polynomial.eval₂_reflect_mul_pow (algebraMap L F) x⁻¹ N p hpN
    rwa [hxinvinv] at this

  have heq : Polynomial.aeval x (p.reflect N) = Polynomial.aeval x (c * Polynomial.X ^ (N - n)) := by
    have hxN0 : (x ^ N : F) ≠ 0 := pow_ne_zero N hx0
    have h1 : Polynomial.aeval x (p.reflect N) * (x⁻¹) ^ N * x ^ N =
        Polynomial.aeval x c * (x ^ n)⁻¹ * x ^ N := by rw [hrefl, hp]
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hx0, one_pow, mul_one] at h1
    rw [h1, map_mul, Polynomial.aeval_X_pow, mul_assoc, mul_comm ((x ^ n)⁻¹) (x ^ N),
      ← pow_sub₀ x hx0 hnN]

  have hpoly : p.reflect N = c * Polynomial.X ^ (N - n) :=
    (transcendental_iff_injective.mp hxL) heq

  have hdeg : c.natDegree + (N - n) ≤ N := by
    have hXne : (Polynomial.X : Polynomial L) ^ (N - n) ≠ 0 :=
      pow_ne_zero _ Polynomial.X_ne_zero
    calc c.natDegree + (N - n)
        = (c * Polynomial.X ^ (N - n)).natDegree := by
          rw [Polynomial.natDegree_mul hc0 hXne, Polynomial.natDegree_X_pow]
      _ = (p.reflect N).natDegree := by rw [hpoly]
      _ ≤ max N p.natDegree := Polynomial.natDegree_reflect_le
      _ = N := max_eq_left hpN
  omega

end S_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv
end P2MW
export P2MW.S_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv (solution)
