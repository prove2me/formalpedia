-- Prove2me | solution 1 for QEC.Coding.f256RMFE_ternary_reverse_mul
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:52:01.240891+00:00
-- url     : https://prove2.me/submissions/3368520a-ce3f-4832-a02c-90b297fd4a4e

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Tactic
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding

private theorem f256RMFEphi_apply (bit : ZMod 2) :
    f256RMFEphi bit = algebraMap (ZMod 2) F256 bit := by
  rw [f256RMFEphi, Algebra.linearMap_apply]

private theorem f256RMFEpsi_apply (x : F256) :
    f256RMFEpsi x = Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3 * x) := by
  rw [f256RMFEpsi, LinearMap.comp_apply, LinearMap.mulLeft_apply]

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

private theorem f256RMFEpsi_phi (bit : ZMod 2) :
    f256RMFEpsi (f256RMFEphi bit) = bit := by
  calc
    f256RMFEpsi (f256RMFEphi bit) =
        bit * Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3) := by
          rw [f256RMFEpsi_apply, f256RMFEphi_apply]
          simpa [Algebra.smul_def, mul_comm] using
            (Algebra.trace (ZMod 2) F256).map_smul bit (f256Alpha ^ 3)
    _ = bit := by rw [f256TraceAlphaCubed, mul_one]

theorem solution (x y z : ZMod 2) :
    f256RMFEpsi (f256RMFEphi x * f256RMFEphi y * f256RMFEphi z) = x * y * z := by
  calc
    f256RMFEpsi (f256RMFEphi x * f256RMFEphi y * f256RMFEphi z) =
        f256RMFEpsi (f256RMFEphi (x * y * z)) := by
          congr 1
          simp only [f256RMFEphi_apply]
          rw [← map_mul, ← map_mul]
    _ = x * y * z := f256RMFEpsi_phi (x * y * z)
