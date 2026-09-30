-- Prove2me | solution 1 for TranscendenceTheory.punctual_ideal_finite_jet_characterization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T04:27:00.508832+00:00
-- url     : https://prove2.me/submissions/b0d48787-e147-40e8-be7c-5b0f4ced6961

import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Theorems.Thm_TranscendenceTheory_finite_zero_locus_quotient_geometry


noncomputable section

namespace TranscendenceTheory

/-- A nilpotent ideal in a finite algebra is killed by the vector-space dimension. -/
theorem nilpotent_ideal_pow_finrank_eq_bot
    (K A : Type*) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (J : Ideal A) (hJ : IsNilpotent J) : J ^ Module.finrank K A = ⊥ := by
  obtain ⟨N, hN⟩ := hJ
  have hstep (n : ℕ) (hn : J ^ n ≠ ⊥) : J ^ (n + 1) < J ^ n := by
    refine lt_of_le_of_ne (Ideal.pow_le_pow_right (Nat.le_succ n)) ?_
    intro heq
    have hstable (k : ℕ) : J ^ (n + k) = J ^ n := by
      induction k with
      | zero => simp
      | succ k hk =>
          rw [Nat.add_succ, pow_succ, hk, ← pow_succ, heq]
    have hz : J ^ (n + N) = ⊥ := by
      rw [pow_add, hN]
      simp
    exact hn ((hstable N).symm.trans hz)
  have hbound (n : ℕ) (hn : J ^ n ≠ ⊥) :
      n + Module.finrank K ((J ^ n).restrictScalars K) ≤ Module.finrank K A := by
    induction n with
    | zero =>
        rw [pow_zero, Ideal.one_eq_top, Submodule.restrictScalars_top,
          finrank_top, zero_add]
    | succ n ih =>
        have hprev : J ^ n ≠ ⊥ := by
          intro h
          apply hn
          rw [pow_succ, h]
          simp
        have hlt := Submodule.finrank_lt_finrank_of_lt
          ((Submodule.restrictScalars_lt K).mpr (hstep n hprev))
        have hi := ih hprev
        omega
  by_contra hne
  have hdim := hbound (Module.finrank K A) hne
  have hz : Module.finrank K ((J ^ Module.finrank K A).restrictScalars K) = 0 := by omega
  exact hne ((Submodule.restrictScalars_inj K A A).mp
    (Submodule.finrank_eq_zero.mp hz))

/-- Every ideal with a finite-dimensional quotient contains the dimension-th power
of its radical. This exponent is independent of a choice of generators. -/
theorem finite_quotient_radical_power_bound
    (K R : Type*) [Field K] [CommRing R] [Algebra K R]
    (I : Ideal R) [Module.Finite K (R ⧸ I)] :
    I.radical ^ Module.finrank K (R ⧸ I) ≤ I := by
  let A := R ⧸ I
  let : IsArtinianRing A := IsArtinianRing.of_finite K A
  have he : I.radical.map (Ideal.Quotient.mk I) = nilradical A := by
    rw [Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective (by simp),
      Ideal.map_quotient_self]
    rfl
  have hpow := nilpotent_ideal_pow_finrank_eq_bot K A (nilradical A)
    IsArtinianRing.isNilpotent_nilradical
  have hmap : (I.radical ^ Module.finrank K A).map (Ideal.Quotient.mk I) = ⊥ := by
    rw [Ideal.map_pow, he, hpow]
  have hle := (Ideal.map_le_iff_le_comap).mp (le_of_eq hmap)
  simpa only [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hle

end TranscendenceTheory


noncomputable section
namespace TranscendenceTheory
open MvPolynomial

private theorem singleton_zeroLocus_of_power_sandwich
    (K σ : Type*) [Field K] (I : Ideal (MvPolynomial σ K)) (x : σ → K) (n : ℕ)
    (hpow : (vanishingIdeal K {x}) ^ n ≤ I) (hle : I ≤ vanishingIdeal K {x}) :
    zeroLocus K I = {x} := by
  ext y
  constructor
  · intro hy
    apply Set.mem_singleton_iff.mpr
    funext i
    have hp : X i - C (x i) ∈ vanishingIdeal K {x} := by
      rw [mem_vanishingIdeal_singleton_iff]
      simp
    have hz := hy ((X i - C (x i)) ^ n) (hpow (Ideal.pow_mem_pow hp n))
    have hzero : (y i - x i) ^ n = 0 := by simpa using hz
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero)
  · intro hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    intro p hp
    exact (mem_vanishingIdeal_singleton_iff x p).mp (hle hp)


end TranscendenceTheory

open TranscendenceTheory MvPolynomial

theorem solution
    (K σ : Type*) [Field K] [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (x : σ → K) :
    (zeroLocus K I = {x} ↔
      (vanishingIdeal K {x}) ^ Module.finrank K (MvPolynomial σ K ⧸ I) ≤ I ∧
        I ≤ vanishingIdeal K {x}) ∧
    (zeroLocus K I = {x} →
      0 < Module.finrank K (MvPolynomial σ K ⧸ I) ∧
      Module.Finite K (MvPolynomial σ K ⧸
        (vanishingIdeal K {x}) ^ Module.finrank K (MvPolynomial σ K ⧸ I)) ∧
      I = (I.map (Ideal.Quotient.mk
        ((vanishingIdeal K {x}) ^ Module.finrank K (MvPolynomial σ K ⧸ I)))).comap
          (Ideal.Quotient.mk
            ((vanishingIdeal K {x}) ^ Module.finrank K (MvPolynomial σ K ⧸ I)))) := by
  have hiff : zeroLocus K I = {x} ↔
      (vanishingIdeal K {x}) ^ Module.finrank K (MvPolynomial σ K ⧸ I) ≤ I ∧
        I ≤ vanishingIdeal K {x} := by
    constructor
    · intro hz
      let : Module.Finite K (MvPolynomial σ K ⧸ I) :=
        (finite_zero_locus_quotient_geometry K σ I).1.mpr (hz ▸ Set.finite_singleton x)
      have hrad : I.radical = vanishingIdeal K {x} := by
        rw [← vanishingIdeal_zeroLocus_eq_radical (K := K), hz]
      refine ⟨?_, ?_⟩
      · simpa only [hrad] using finite_quotient_radical_power_bound K (MvPolynomial σ K) I
      · exact hrad ▸ Ideal.le_radical
    · rintro ⟨hpow, hle⟩
      exact singleton_zeroLocus_of_power_sandwich K σ I x _ hpow hle
  refine ⟨hiff, ?_⟩
  intro hz
  obtain ⟨hpow, hle⟩ := hiff.mp hz
  have hd : 0 < Module.finrank K (MvPolynomial σ K ⧸ I) := by
    by_contra h
    have he : Module.finrank K (MvPolynomial σ K ⧸ I) = 0 := Nat.eq_zero_of_not_pos h
    rw [he, pow_zero, Ideal.one_eq_top] at hpow
    exact (inferInstance : (vanishingIdeal K {x}).IsMaximal).ne_top
      (top_le_iff.mp (hpow.trans hle))
  refine ⟨hd, ?_, (Ideal.comap_map_mk hpow).symm⟩
  apply (finite_zero_locus_quotient_geometry K σ _).1.mpr
  rw [singleton_zeroLocus_of_power_sandwich K σ _ x _ le_rfl
    (Ideal.pow_le_self (Nat.ne_zero_of_lt hd))]
  exact Set.finite_singleton x
