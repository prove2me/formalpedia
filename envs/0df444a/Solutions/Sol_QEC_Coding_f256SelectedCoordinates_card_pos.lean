-- Prove2me | solution 1 for QEC.Coding.f256SelectedCoordinates_card_pos
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:50:11.291967+00:00
-- url     : https://prove2.me/submissions/394cb8c3-03c0-406f-9c20-14aa6cc07cbd

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Tactic
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding

private theorem f256MFEPsi_apply (v : Fin 512 → ZMod 2) :
    f256MFEPsi v =
      ∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8,
        v (f256MFEIndex i j k) •
          (f256PolynomialBasis i * f256PolynomialBasis j * f256PolynomialBasis k) := rfl

private theorem f256PolynomialBasis_apply (i : Fin 8) :
    f256PolynomialBasis i = f256Alpha ^ (i : ℕ) := by
  rw [f256PolynomialBasis, Module.Basis.reindex_apply,
    (AdjoinRoot.powerBasis' f256Modulus_monic).basis_eq_pow]
  rfl

private theorem f256SelectorQ0_eq_index_iff (i j k : Fin 8) :
    f256SelectorQ0 = f256MFEIndex i j k ↔ i = 0 ∧ j = 0 ∧ k = 0 := by
  constructor
  · intro h
    have hindex : (0, (0, 0)) = (i, (j, k)) := f256MFEIndexEquiv.injective (by
      simpa [f256SelectorQ0, f256MFEIndex] using h)
    exact ⟨(congrArg Prod.fst hindex).symm, (congrArg Prod.fst (congrArg Prod.snd hindex)).symm,
      (congrArg Prod.snd (congrArg Prod.snd hindex)).symm⟩
  · rintro ⟨hi, hj, hk⟩
    subst i; subst j; subst k; rfl

private theorem f256MFEIndex_eq_selectorQ0_iff (i j k : Fin 8) :
    f256MFEIndex i j k = f256SelectorQ0 ↔ i = 0 ∧ j = 0 ∧ k = 0 := by
  constructor
  · intro h; exact (f256SelectorQ0_eq_index_iff i j k).mp h.symm
  · intro h; exact ((f256SelectorQ0_eq_index_iff i j k).mpr h).symm

private theorem f256MFEPsi_single_q0 :
    f256MFEPsi (Pi.single f256SelectorQ0 1) = 1 := by
  rw [f256MFEPsi_apply]
  classical
  simp [Pi.single_apply, f256MFEIndex_eq_selectorQ0_iff, f256PolynomialBasis_apply]
  rw [Fintype.sum_eq_single (0 : Fin 8)]
  · rw [Fintype.sum_eq_single (0 : Fin 8)]
    · rw [Fintype.sum_eq_single (0 : Fin 8)]
      · simp
      · intro k hk; simp [hk]
    · intro j hj; simp [hj]
  · intro i hi; simp [hi]

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

private theorem f256RMFEpsi_one : f256RMFEpsi 1 = 1 := by
  simpa [f256RMFEphi_apply] using f256RMFEpsi_phi (1 : ZMod 2)

private theorem f256SelectorFunctional_apply (v : Fin 512 → ZMod 2) :
    f256SelectorFunctional v = f256RMFEpsi (f256MFEPsi v) := rfl


private theorem f256SelectorCoefficient_q0 : f256SelectorCoefficient f256SelectorQ0 = 1 := by
  rw [f256SelectorCoefficient, f256SelectorFunctional_apply, f256MFEPsi_single_q0]
  exact f256RMFEpsi_one

private theorem f256SelectorQ0_mem_selectedCoordinates :
    f256SelectorQ0 ∈ f256SelectedCoordinates := by
  simp [f256SelectedCoordinates, f256SelectorCoefficient_q0]

private theorem f256SelectedCoordinates_nonempty : f256SelectedCoordinates.Nonempty :=
  ⟨f256SelectorQ0, f256SelectorQ0_mem_selectedCoordinates⟩

theorem solution : 0 < f256SelectedCoordinates.card :=
  Finset.card_pos.mpr f256SelectedCoordinates_nonempty
