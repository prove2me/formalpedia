-- Prove2me | solution 1 for ShiShallow.conj_majority_inclusion_exclusion_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T23:04:48.480444+00:00
-- url     : https://prove2.me/submissions/76cb082e-14ad-4d34-933f-028f97f6cf74

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

open ShiShallow

/-- A one-sided inverse of a square matrix is two-sided. -/
private theorem mul_star_self_of_star_mul_self' {n : ℕ} (U : Op n)
    (hU : star U * U = 1) : U * star U = 1 := by
  first
    | (exact mul_eq_one_comm.mp hU; done)
    | (exact Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_unitaryGroup_iff'.mpr hU); done)
    | (rw [mul_eq_one_comm]; exact hU; done)

/-- Conjugation by a unitary is multiplicative. -/
private theorem shiFin2_conj_mul {n : ℕ} (A : Op n) (hA : star A * A = 1) (X Y : Op n) :
    (star A * X * A) * (star A * Y * A) = star A * (X * Y) * A := by
  have h : A * star A = (1 : Op n) := mul_star_self_of_star_mul_self' A hA
  calc (star A * X * A) * (star A * Y * A)
      = star A * X * (A * star A) * Y * A := by
        simp only [mul_assoc]
    _ = star A * (X * Y) * A := by
        rw [h]
        simp only [mul_one, mul_assoc]

theorem solution {n : ℕ} (A P Q R : Op n)
    (hA : star A * A = (1 : Op n)) :
    star A * (P * Q + Q * R + R * P - 2 * (P * Q * R)) * A
      = (star A * P * A) * (star A * Q * A)
        + (star A * Q * A) * (star A * R * A)
        + (star A * R * A) * (star A * P * A)
        - 2 * ((star A * P * A) * (star A * Q * A) * (star A * R * A)) := by
  have h2 : ∀ X Y : Op n, (star A * X * A) * (star A * Y * A) = star A * (X * Y) * A :=
    fun X Y => shiFin2_conj_mul A hA X Y
  rw [h2 P Q, h2 Q R, h2 R P, h2 (P * Q) R]
  first
    | (noncomm_ring; done)
    | (simp only [two_mul, mul_add, add_mul, mul_sub, sub_mul, mul_assoc]; done)
    | (rw [two_mul, two_mul]
       simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc]
       done)
    | (rw [two_mul, two_mul]
       noncomm_ring
       done)
    | (simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, two_mul,
         mul_assoc]
       done)
