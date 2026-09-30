-- Prove2me | solution 1 for TranscendenceTheory.pure_power_local_multiplicity_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T20:05:48.833275+00:00
-- url     : https://prove2.me/submissions/b1b5d51c-2fe2-4f5a-a602-e3e21c68c360

import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_TranscendenceTheory_finite_algebra_local_multiplicity_dimension

noncomputable section

namespace TranscendenceTheory

open MvPolynomial

theorem pure_power_quotient_dimension
    (K : Type*) [Field K] (σ : Type*) [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (o : MonomialOrder σ)
    (d : σ → ℕ) (b : σ → MvPolynomial σ K)
    (hb : ∀ i, b i ∈ I)
    (hu : ∀ i, IsUnit (o.leadingCoeff (b i)))
    (hd : ∀ i, o.degree (b i) = Finsupp.single i (d i)) :
    Module.Finite K (MvPolynomial σ K ⧸ I) ∧
      Module.finrank K (MvPolynomial σ K ⧸ I) ≤ ∏ i, d i := by
  classical
  let q := Ideal.Quotient.mkₐ K I
  let v : (∀ i, Fin (d i)) → (MvPolynomial σ K ⧸ I) :=
    fun a => q (monomial (Finsupp.equivFunOnFinite.symm (fun i => (a i).val)) 1)
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨g, r, hfr, -, hr⟩ := o.div hu f
    have hg : Finsupp.linearCombination (MvPolynomial σ K) b g ∈ I := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      exact I.sum_mem fun i _ => I.mul_mem_left _ (hb i)
    have hqr : q f = q r := by
      rw [hfr, map_add]
      have hz : q (Finsupp.linearCombination (MvPolynomial σ K) b g) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hg
      rw [hz, zero_add]
    change q f ∈ Submodule.span K (Set.range v)
    rw [hqr, r.as_sum, map_sum]
    apply Submodule.sum_mem
    intro c hc
    have hcd : ∀ i, c i < d i := by
      intro i
      have h := hr c hc i
      rw [hd i, Finsupp.single_le_iff] at h
      exact lt_of_not_ge h
    let a : ∀ i, Fin (d i) := fun i => ⟨c i, hcd i⟩
    have he : Finsupp.equivFunOnFinite.symm (fun i => (a i).val) = c := by
      ext i
      simp [a]
    have hv : q (monomial c 1) ∈ Submodule.span K (Set.range v) := by
      apply Submodule.subset_span
      exact ⟨a, by dsimp [v]; rw [he]⟩
    have hcoeff : q (monomial c (coeff c r)) = coeff c r • q (monomial c 1) := by
      rw [← map_smul]
      apply congrArg q
      simp only [smul_monomial, smul_eq_mul, mul_one]
    rw [hcoeff]
    exact Submodule.smul_mem _ _ hv
  constructor
  · rw [Module.finite_def, ← hspan]
    exact Submodule.fg_span (Set.finite_range v)
  · have h := finrank_le_of_span_eq_top hspan
    simpa using h


end TranscendenceTheory

open TranscendenceTheory

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (σ : Type*) [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (o : MonomialOrder σ)
    (d : σ → ℕ) (b : σ → MvPolynomial σ K)
    (hb : ∀ i, b i ∈ I)
    (hu : ∀ i, IsUnit (o.leadingCoeff (b i)))
    (hd : ∀ i, o.degree (b i) = Finsupp.single i (d i)) :
    Module.Finite K (MvPolynomial σ K ⧸ I) ∧
      Module.finrank K (MvPolynomial σ K ⧸ I) ≤ ∏ i, d i ∧
      (∀ p : PrimeSpectrum (MvPolynomial σ K ⧸ I),
        Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal) ≠ ⊤) ∧
      ∀ (ι : Type*) [Fintype ι]
        (p : ι → PrimeSpectrum (MvPolynomial σ K ⧸ I)), Function.Injective p →
        (∑ i, (Module.length (Localization.AtPrime (p i).asIdeal)
          (Localization.AtPrime (p i).asIdeal)).toNat) ≤ ∏ i, d i ∧
        ∀ e : ℕ, (∀ i, e ≤ (Module.length (Localization.AtPrime (p i).asIdeal)
          (Localization.AtPrime (p i).asIdeal)).toNat) →
          Fintype.card ι * e ≤ ∏ i, d i := by
  classical
  obtain ⟨hfinite, hdim⟩ := pure_power_quotient_dimension K σ I o d b hb hu hd
  let := hfinite
  obtain ⟨hlength, hsum⟩ :=
    finite_algebra_local_multiplicity_dimension K (MvPolynomial σ K ⧸ I)
  refine ⟨hfinite, hdim, hlength, ?_⟩
  intro ι _ p hp
  have htotal := ((hsum ι p hp).1).trans hdim
  refine ⟨htotal, ?_⟩
  intro e he
  calc
    Fintype.card ι * e = ∑ _i : ι, e := by simp
    _ ≤ ∑ i, (Module.length (Localization.AtPrime (p i).asIdeal)
      (Localization.AtPrime (p i).asIdeal)).toNat :=
        Finset.sum_le_sum fun i _ => he i
    _ ≤ ∏ i, d i := htotal
