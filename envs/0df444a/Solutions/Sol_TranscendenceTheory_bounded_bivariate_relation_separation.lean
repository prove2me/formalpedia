-- Prove2me | solution 1 for TranscendenceTheory.bounded_bivariate_relation_separation
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T16:43:50.196923+00:00
-- url     : https://prove2.me/submissions/8c5d997c-2f54-437c-ae70-a2ce65d6c01a

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms

noncomputable section
open Polynomial
open scoped Classical

private lemma linear_factor_of_ker_le
    {K V A L : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup A] [Module K A]
    [AddCommGroup L] [Module K L]
    (E : V →ₗ[K] A) (e : V →ₗ[K] L) (h : E.ker ≤ e.ker) :
    ∃ T : A →ₗ[K] L, T.comp E = e := by
  let q : E.range →ₗ[K] L :=
    (E.ker.liftQ e h).comp E.quotKerEquivRange.symm.toLinearMap
  obtain ⟨T, hT⟩ := q.exists_extend
  refine ⟨T, ?_⟩
  ext p
  have ht := LinearMap.congr_fun hT ⟨E p, LinearMap.mem_range_self E p⟩
  simpa [q, LinearMap.comp_apply, E.quotKerEquivRange_symm_apply_image] using ht

private lemma map_bounded_bivariate_evaluation
    {K A L : Type*} [Field K] [CommRing A] [Algebra K A]
    [CommRing L] [Algebra K L] (x y : A) (u v : L) (b s : ℕ)
    (T : A →ₗ[K] L)
    (hT : ∀ i ≤ s, ∀ j ≤ b, T (x ^ j * y ^ i) = u ^ j * v ^ i)
    (P : Polynomial (Polynomial K))
    (hs : P.natDegree ≤ s) (hb : ∀ i, (P.coeff i).natDegree ≤ b) :
    T (P.eval₂ (Polynomial.aeval x).toRingHom y) =
      P.eval₂ (Polynomial.aeval u).toRingHom v := by
  rw [eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hs),
    eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hs), map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le (hb i)),
    aeval_eq_sum_range' (Nat.lt_succ_of_le (hb i)),
    Finset.sum_mul, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [smul_mul_assoc, map_smul]
  rw [hT i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]

private def bounded_bivariate_space
    (K : Type*) [Field K] (b s : ℕ) : Submodule K (Polynomial (Polynomial K)) :=
  { carrier := {P | P.natDegree ≤ s ∧ ∀ i, (P.coeff i).natDegree ≤ b}
    zero_mem' := by simp
    add_mem' := by
      intro P Q hP hQ
      refine ⟨(natDegree_add_le P Q).trans (max_le hP.1 hQ.1), ?_⟩
      intro i
      rw [coeff_add]
      exact (natDegree_add_le (P.coeff i) (Q.coeff i)).trans
        (max_le (hP.2 i) (hQ.2 i))
    smul_mem' := by
      intro c P hP
      refine ⟨(natDegree_smul_le c P).trans hP.1, ?_⟩
      intro i
      rw [coeff_smul]
      exact (natDegree_smul_le c (P.coeff i)).trans (hP.2 i) }

theorem solution
    (K A L : Type*) [Field K] [CommRing A] [Algebra K A]
    [CommRing L] [Algebra K L] (x y : A) (u v : L) (b s : ℕ) :
    (∃ P : Polynomial (Polynomial K),
      P.natDegree ≤ s ∧ (∀ i, (P.coeff i).natDegree ≤ b) ∧
        P.eval₂ (Polynomial.aeval x).toRingHom y = 0 ∧
        P.eval₂ (Polynomial.aeval u).toRingHom v ≠ 0) ↔
      ¬ ∃ T : A →ₗ[K] L,
        ∀ i ≤ s, ∀ j ≤ b, T (x ^ j * y ^ i) = u ^ j * v ^ i := by
  classical
  constructor
  · rintro ⟨P, hs, hb, hzero, hnonzero⟩ ⟨T, hT⟩
    apply hnonzero
    rw [← map_bounded_bivariate_evaluation x y u v b s T hT P hs hb,
      hzero, map_zero]
  · intro hn
    by_contra hex
    push Not at hex
    let W := bounded_bivariate_space K b s
    let E0 : Polynomial (Polynomial K) →ₐ[K] A :=
      Polynomial.aevalTower (Polynomial.aeval x) y
    let e0 : Polynomial (Polynomial K) →ₐ[K] L :=
      Polynomial.aevalTower (Polynomial.aeval u) v
    let E : W →ₗ[K] A := E0.toLinearMap.comp W.subtype
    let e : W →ₗ[K] L := e0.toLinearMap.comp W.subtype
    have hk : E.ker ≤ e.ker := fun P hp => hex P.val P.property.1 P.property.2 hp
    obtain ⟨T, hT⟩ := linear_factor_of_ker_le (K := K) (V := W) (A := A) (L := L) E e hk
    apply hn
    refine ⟨T, ?_⟩
    intro i hi j hj
    let P : Polynomial (Polynomial K) := C (X ^ j) * X ^ i
    have hP : P ∈ W := by
      refine ⟨(natDegree_C_mul_X_pow_le (X ^ j) i).trans hi, ?_⟩
      intro k
      dsimp [P]
      rw [coeff_C_mul_X_pow]
      split_ifs
      · simpa using hj
      · simp
    have ht := LinearMap.congr_fun hT ⟨P, hP⟩
    simpa [E, e, E0, e0, P, aevalTower_C, aevalTower_X] using ht
