-- Prove2me | solution 1 for QEC.Coding.f256TraceAlphaCubedSquare
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:52:02.468302+00:00
-- url     : https://prove2.me/submissions/0a6c1eb4-5a20-443a-bd92-b66ef3136f8e

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Tactic
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding

private theorem f256_finrank : Module.finrank (ZMod 2) F256 = 8 := by
  simpa [F256, f256Modulus_natDegree] using
    (AdjoinRoot.powerBasis' f256Modulus_monic).finrank

private theorem f256Alpha_pow_eq_mk (k : ℕ) :
    f256Alpha ^ k = AdjoinRoot.mk f256Modulus (X ^ k) := by
  simp [f256Alpha, ← AdjoinRoot.mk_X]

private theorem f256Alpha_pow_seventeen : f256Alpha ^ 17 = 1 := by
  rw [f256Alpha_pow_eq_mk, ← (AdjoinRoot.mk f256Modulus).map_one, AdjoinRoot.mk_eq_mk]
  refine ⟨(X + 1) * (X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4 + X ^ 2 + X + 1), ?_⟩
  simp only [f256Modulus]; ring_nf; reduce_mod_char

private theorem f256_mk_eq_of_dvd_sub {p q : Polynomial (ZMod 2)}
    (h : f256Modulus ∣ p - q) :
    AdjoinRoot.mk f256Modulus p = AdjoinRoot.mk f256Modulus q := by
  calc
    AdjoinRoot.mk f256Modulus p =
        AdjoinRoot.mk f256Modulus (p %ₘ f256Modulus) := by
          symm
          simpa only [AdjoinRoot.modByMonicHom_mk] using
            (AdjoinRoot.mk_leftInverse f256Modulus_monic (AdjoinRoot.mk f256Modulus p))
    _ = AdjoinRoot.mk f256Modulus (q %ₘ f256Modulus) := by
          rw [Polynomial.modByMonic_eq_of_dvd_sub f256Modulus_monic h]
    _ = AdjoinRoot.mk f256Modulus q := by
          simpa only [AdjoinRoot.modByMonicHom_mk] using
            (AdjoinRoot.mk_leftInverse f256Modulus_monic (AdjoinRoot.mk f256Modulus q))

private theorem f256_frobenius_sum_three :
    f256Alpha ^ 3 + f256Alpha ^ 6 + f256Alpha ^ 12 + f256Alpha ^ 7 +
      f256Alpha ^ 14 + f256Alpha ^ 11 + f256Alpha ^ 5 + f256Alpha ^ 10 = 1 := by
  have hmk :
      AdjoinRoot.mk f256Modulus
          (X ^ 14 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3) =
        AdjoinRoot.mk f256Modulus 1 := by
    apply f256_mk_eq_of_dvd_sub
    refine ⟨X ^ 6 + X ^ 4 + 1, ?_⟩
    simp only [f256Modulus]; ring_nf; reduce_mod_char
  simpa only [map_add, map_pow, AdjoinRoot.mk_X, map_one, f256Alpha,
    add_comm, add_left_comm, add_assoc] using hmk

private theorem f256TraceAlphaCubed :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3) = 1 := by
  apply (algebraMap (ZMod 2) F256).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [Finset.sum_range_succ, f256_finrank, Nat.card_zmod]
  simp only [← pow_mul]
  rw [pow_eq_pow_mod 384 f256Alpha_pow_seventeen, pow_eq_pow_mod 192 f256Alpha_pow_seventeen,
    pow_eq_pow_mod 96 f256Alpha_pow_seventeen, pow_eq_pow_mod 48 f256Alpha_pow_seventeen,
    pow_eq_pow_mod 24 f256Alpha_pow_seventeen]
  simpa only [Nat.reduceMod] using f256_frobenius_sum_three

private theorem f256Alpha_pow_256_mul (k : ℕ) :
    f256Alpha ^ (256 * k) = f256Alpha ^ k := by
  calc
    f256Alpha ^ (256 * k) = f256Alpha ^ (k + 17 * (15 * k)) := by congr 1; ring
    _ = f256Alpha ^ k * f256Alpha ^ (17 * (15 * k)) := by rw [pow_add]
    _ = f256Alpha ^ k * (f256Alpha ^ 17) ^ (15 * k) := by rw [pow_mul]
    _ = f256Alpha ^ k := by rw [f256Alpha_pow_seventeen, one_pow, mul_one]

private theorem f256_trace_alpha_pow_two_mul (k : ℕ) :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ (2 * k)) =
      Algebra.trace (ZMod 2) F256 (f256Alpha ^ k) := by
  apply (algebraMap (ZMod 2) F256).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow, FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [Finset.sum_range_succ, f256_finrank, Nat.card_zmod]
  simp only [← pow_mul]
  have h256 : (2 * k) * 128 = 256 * k := by ring
  rw [h256, f256Alpha_pow_256_mul]
  ring

theorem solution :
    Algebra.trace (ZMod 2) F256 ((f256Alpha ^ 3) ^ 2) = 1 := by
  have h : (f256Alpha ^ 3) ^ 2 = f256Alpha ^ (3 * 2) := (pow_mul f256Alpha 3 2).symm
  rw [h]
  norm_num
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 6) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3) := by
          simpa using f256_trace_alpha_pow_two_mul 3
    _ = 1 := f256TraceAlphaCubed
