-- Prove2me | solution 1 for QEC.Coding.f256PolynomialTraceMatrix_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:49:03.406268+00:00
-- url     : https://prove2.me/submissions/3111a1a5-b792-40cc-b04f-18b801c99486

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Field
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Theorems.Thm_QEC_Coding_f256Alpha_pow_seventeen
import Theorems.Thm_QEC_Coding_f256PolynomialBasis_apply
import Theorems.Thm_QEC_Coding_f256_finrank

section
open Polynomial
open scoped Matrix
namespace QEC.Coding
private theorem f256_trace_alpha_pow_0 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 0) = 0 := by
  apply (algebraMap (ZMod 2) F256).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [f256_finrank, Nat.card_zmod]
  exact CharP.ofNat_eq_zero' (R := F256) 2 8 (by norm_num)
private theorem f256_mk_eq_of_dvd_sub {p q : Polynomial (ZMod 2)}
    (h : f256Modulus ∣ p - q) :
    AdjoinRoot.mk f256Modulus p = AdjoinRoot.mk f256Modulus q := by
  calc
    AdjoinRoot.mk f256Modulus p =
        AdjoinRoot.mk f256Modulus (p %ₘ f256Modulus) := by
          symm
          simpa only [AdjoinRoot.modByMonicHom_mk] using
            (AdjoinRoot.mk_leftInverse f256Modulus_monic
              (AdjoinRoot.mk f256Modulus p))
    _ = AdjoinRoot.mk f256Modulus (q %ₘ f256Modulus) := by
          rw [Polynomial.modByMonic_eq_of_dvd_sub f256Modulus_monic h]
    _ = AdjoinRoot.mk f256Modulus q := by
          simpa only [AdjoinRoot.modByMonicHom_mk] using
            (AdjoinRoot.mk_leftInverse f256Modulus_monic
              (AdjoinRoot.mk f256Modulus q))
private theorem f256_frobenius_sum_one :
    f256Alpha + f256Alpha ^ 2 + f256Alpha ^ 4 + f256Alpha ^ 8 +
      f256Alpha ^ 16 + f256Alpha ^ 15 + f256Alpha ^ 13 + f256Alpha ^ 9 = 0 := by
  have hmk :
      AdjoinRoot.mk f256Modulus
          (X ^ 16 + X ^ 15 + X ^ 13 + X ^ 9 + X ^ 8 + X ^ 4 + X ^ 2 + X) =
        AdjoinRoot.mk f256Modulus 0 := by
    apply f256_mk_eq_of_dvd_sub
    refine ⟨X ^ 8 + X ^ 7 + X ^ 2 + X, ?_⟩
    simp only [f256Modulus]
    ring_nf
    reduce_mod_char
  simpa only [map_add, map_pow, AdjoinRoot.mk_X, map_zero, f256Alpha,
    add_comm, add_left_comm, add_assoc] using hmk
private theorem f256_trace_alpha_pow_1 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 1) = 0 := by
  apply (algebraMap (ZMod 2) F256).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [Finset.sum_range_succ, f256_finrank, Nat.card_zmod]
  rw [pow_eq_pow_mod 128 f256Alpha_pow_seventeen,
    pow_eq_pow_mod 64 f256Alpha_pow_seventeen,
    pow_eq_pow_mod 32 f256Alpha_pow_seventeen]
  simpa only [Nat.reduceMod, pow_one] using f256_frobenius_sum_one
private theorem f256_frobenius_sum_three :
    f256Alpha ^ 3 + f256Alpha ^ 6 + f256Alpha ^ 12 + f256Alpha ^ 7 +
      f256Alpha ^ 14 + f256Alpha ^ 11 + f256Alpha ^ 5 + f256Alpha ^ 10 = 1 := by
  have hmk :
      AdjoinRoot.mk f256Modulus
          (X ^ 14 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3) =
        AdjoinRoot.mk f256Modulus 1 := by
    apply f256_mk_eq_of_dvd_sub
    refine ⟨X ^ 6 + X ^ 4 + 1, ?_⟩
    simp only [f256Modulus]
    ring_nf
    reduce_mod_char
  simpa only [map_add, map_pow, AdjoinRoot.mk_X, map_one, f256Alpha,
    add_comm, add_left_comm, add_assoc] using hmk
private theorem f256_trace_alpha_pow_3 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3) = 1 := by
  apply (algebraMap (ZMod 2) F256).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [Finset.sum_range_succ, f256_finrank, Nat.card_zmod]
  simp only [← pow_mul]
  rw [pow_eq_pow_mod 384 f256Alpha_pow_seventeen,
    pow_eq_pow_mod 192 f256Alpha_pow_seventeen,
    pow_eq_pow_mod 96 f256Alpha_pow_seventeen,
    pow_eq_pow_mod 48 f256Alpha_pow_seventeen,
    pow_eq_pow_mod 24 f256Alpha_pow_seventeen]
  simpa only [Nat.reduceMod] using f256_frobenius_sum_three
private theorem f256Alpha_pow_256_mul (k : ℕ) :
    f256Alpha ^ (256 * k) = f256Alpha ^ k := by
  calc
    f256Alpha ^ (256 * k) = f256Alpha ^ (k + 17 * (15 * k)) := by
      congr 1
      ring
    _ = f256Alpha ^ k * f256Alpha ^ (17 * (15 * k)) := by
      rw [pow_add]
    _ = f256Alpha ^ k * (f256Alpha ^ 17) ^ (15 * k) := by
      rw [pow_mul]
    _ = f256Alpha ^ k := by rw [f256Alpha_pow_seventeen, one_pow, mul_one]
private theorem f256_trace_alpha_pow_two_mul (k : ℕ) :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ (2 * k)) =
      Algebra.trace (ZMod 2) F256 (f256Alpha ^ k) := by
  apply (algebraMap (ZMod 2) F256).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow,
    FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [Finset.sum_range_succ, f256_finrank, Nat.card_zmod]
  simp only [← pow_mul]
  have h256 : (2 * k) * 128 = 256 * k := by ring
  rw [h256, f256Alpha_pow_256_mul]
  ring
private theorem f256_trace_alpha_pow_2 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 2) = 0 := by
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 2) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 1) := by
          simpa using f256_trace_alpha_pow_two_mul 1
    _ = 0 := f256_trace_alpha_pow_1
private theorem f256_trace_alpha_pow_4 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 4) = 0 := by
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 4) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 2) := by
          simpa using f256_trace_alpha_pow_two_mul 2
    _ = 0 := f256_trace_alpha_pow_2
private theorem f256_trace_alpha_pow_8 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 8) = 0 := by
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 8) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 4) := by
          simpa using f256_trace_alpha_pow_two_mul 4
    _ = 0 := f256_trace_alpha_pow_4
private theorem f256_trace_alpha_pow_15 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 15) = 0 := by
  have h32 : f256Alpha ^ 32 = f256Alpha ^ 15 := by
    rw [pow_eq_pow_mod 32 f256Alpha_pow_seventeen]
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 15) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 32) := by rw [h32]
    _ = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 16) := by
          simpa using f256_trace_alpha_pow_two_mul 16
    _ = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 8) := by
          simpa using f256_trace_alpha_pow_two_mul 8
    _ = 0 := f256_trace_alpha_pow_8
private theorem f256_trace_alpha_pow_13 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 13) = 0 := by
  have h30 : f256Alpha ^ 30 = f256Alpha ^ 13 := by
    rw [pow_eq_pow_mod 30 f256Alpha_pow_seventeen]
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 13) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 30) := by rw [h30]
    _ = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 15) := by
          simpa using f256_trace_alpha_pow_two_mul 15
    _ = 0 := f256_trace_alpha_pow_15
private theorem f256_trace_alpha_pow_9 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 9) = 0 := by
  have h26 : f256Alpha ^ 26 = f256Alpha ^ 9 := by
    rw [pow_eq_pow_mod 26 f256Alpha_pow_seventeen]
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 9) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 26) := by rw [h26]
    _ = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 13) := by
          simpa using f256_trace_alpha_pow_two_mul 13
    _ = 0 := f256_trace_alpha_pow_13
private theorem f256_trace_alpha_pow_6 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 6) = 1 := by
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 6) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3) := by
          simpa using f256_trace_alpha_pow_two_mul 3
    _ = 1 := f256_trace_alpha_pow_3
private theorem f256_trace_alpha_pow_12 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 12) = 1 := by
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 12) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 6) := by
          simpa using f256_trace_alpha_pow_two_mul 6
    _ = 1 := f256_trace_alpha_pow_6
private theorem f256_trace_alpha_pow_7 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 7) = 1 := by
  have h24 : f256Alpha ^ 24 = f256Alpha ^ 7 := by
    rw [pow_eq_pow_mod 24 f256Alpha_pow_seventeen]
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 7) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 24) := by rw [h24]
    _ = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 12) := by
          simpa using f256_trace_alpha_pow_two_mul 12
    _ = 1 := f256_trace_alpha_pow_12
private theorem f256_trace_alpha_pow_14 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 14) = 1 := by
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 14) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 7) := by
          simpa using f256_trace_alpha_pow_two_mul 7
    _ = 1 := f256_trace_alpha_pow_7
private theorem f256_trace_alpha_pow_11 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 11) = 1 := by
  have h28 : f256Alpha ^ 28 = f256Alpha ^ 11 := by
    rw [pow_eq_pow_mod 28 f256Alpha_pow_seventeen]
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 11) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 28) := by rw [h28]
    _ = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 14) := by
          simpa using f256_trace_alpha_pow_two_mul 14
    _ = 1 := f256_trace_alpha_pow_14
private theorem f256_trace_alpha_pow_5 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 5) = 1 := by
  have h22 : f256Alpha ^ 22 = f256Alpha ^ 5 := by
    rw [pow_eq_pow_mod 22 f256Alpha_pow_seventeen]
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 5) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 22) := by rw [h22]
    _ = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 11) := by
          simpa using f256_trace_alpha_pow_two_mul 11
    _ = 1 := f256_trace_alpha_pow_11
private theorem f256_trace_alpha_pow_10 :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 10) = 1 := by
  calc
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 10) =
        Algebra.trace (ZMod 2) F256 (f256Alpha ^ 5) := by
          simpa using f256_trace_alpha_pow_two_mul 5
    _ = 1 := f256_trace_alpha_pow_5
end QEC.Coding
end

set_option autoImplicit false
open Polynomial
open scoped Matrix
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    Algebra.traceMatrix (ZMod 2) f256PolynomialBasis = f256PolynomialTraceGram := by
  ext i j
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    f256PolynomialBasis_apply, f256PolynomialBasis_apply, ← pow_add]
  fin_cases i <;> fin_cases j <;>
    norm_num [f256PolynomialTraceGram, f256_trace_alpha_pow_0,
      f256_trace_alpha_pow_1, f256_trace_alpha_pow_2, f256_trace_alpha_pow_3,
      f256_trace_alpha_pow_4, f256_trace_alpha_pow_5, f256_trace_alpha_pow_6,
      f256_trace_alpha_pow_7, f256_trace_alpha_pow_8, f256_trace_alpha_pow_9,
      f256_trace_alpha_pow_10, f256_trace_alpha_pow_11, f256_trace_alpha_pow_12,
      f256_trace_alpha_pow_13, f256_trace_alpha_pow_14] <;>
    first
    | simpa only [pow_zero] using f256_trace_alpha_pow_0
    | simpa only [pow_one] using f256_trace_alpha_pow_1
end QEC.Coding
