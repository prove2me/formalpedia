-- Prove2me | solution 1 for TranscendenceTheory.pure_power_certificate_ideal_elimination
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T02:45:30.16173+00:00
-- url     : https://prove2.me/submissions/bede87bc-c419-45ed-b614-ee6119c6e9d9

import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.FieldTheory.IsAlgClosed.Basic


import Mathlib.RingTheory.Spectrum.Prime.RingHom

import Theorems.Thm_TranscendenceTheory_pure_power_local_multiplicity_bound

noncomputable section

namespace TranscendenceTheory

theorem localization_at_prime_map_surjective
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (p : PrimeSpectrum B) :
    Function.Surjective (Localization.localRingHom
      (p.asIdeal.comap f) p.asIdeal f rfl) := by
  intro y
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.mk'_surjective p.asIdeal.primeCompl y
  obtain ⟨a, ha⟩ := hf b
  obtain ⟨t, ht⟩ := hf s.val
  have htp : t ∈ (p.asIdeal.comap f).primeCompl := by
    change f t ∉ p.asIdeal
    rw [ht]
    exact s.property
  refine ⟨IsLocalization.mk' (Localization.AtPrime (p.asIdeal.comap f)) a ⟨t, htp⟩, ?_⟩
  rw [Localization.localRingHom_mk']
  simpa only [ha, ht] using hbs

/-- A surjection of rings does not increase lengths at corresponding primes. -/
theorem local_length_le_of_surjective
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (p : PrimeSpectrum B) :
    Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) ≤
      Module.length (Localization.AtPrime (p.asIdeal.comap f))
        (Localization.AtPrime (p.asIdeal.comap f)) := by
  let g := Localization.localRingHom (p.asIdeal.comap f) p.asIdeal f rfl
  have hg : Function.Surjective g := localization_at_prime_map_surjective f hf p
  let := g.toAlgebra
  have hle := Module.length_le_of_surjective
    (Algebra.linearMap (Localization.AtPrime (p.asIdeal.comap f))
      (Localization.AtPrime p.asIdeal)) hg
  have he := Module.length_eq_of_surjective
    (M := Localization.AtPrime p.asIdeal) hg
  exact he ▸ hle

end TranscendenceTheory

noncomputable section

namespace TranscendenceTheory

/-- The pure-power certificate polynomials themselves generate an ideal with
the same upper budget and no smaller local multiplicities at the selected primes. -/
theorem pure_power_generated_ideal_transfer
    (K : Type*) [Field K] [IsAlgClosed K] (σ : Type*) [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (o : MonomialOrder σ)
    (d : σ → ℕ) (b : σ → MvPolynomial σ K)
    (hb : ∀ i, b i ∈ I)
    (hu : ∀ i, IsUnit (o.leadingCoeff (b i)))
    (hd : ∀ i, o.degree (b i) = Finsupp.single i (d i)) :
    let J : Ideal (MvPolynomial σ K) := Ideal.span (Set.range b)
    Module.Finite K (MvPolynomial σ K ⧸ J) ∧
      Module.finrank K (MvPolynomial σ K ⧸ J) ≤ ∏ i, d i ∧
      ∀ (ι : Type*) [Fintype ι]
        (p : ι → PrimeSpectrum (MvPolynomial σ K ⧸ I)), Function.Injective p →
        ∃ q : ι → PrimeSpectrum (MvPolynomial σ K ⧸ J),
          Function.Injective q ∧
          (∀ i,
            Module.length (Localization.AtPrime (p i).asIdeal)
              (Localization.AtPrime (p i).asIdeal) ≠ ⊤ ∧
            Module.length (Localization.AtPrime (q i).asIdeal)
              (Localization.AtPrime (q i).asIdeal) ≠ ⊤ ∧
            (Module.length (Localization.AtPrime (p i).asIdeal)
              (Localization.AtPrime (p i).asIdeal)).toNat ≤
            (Module.length (Localization.AtPrime (q i).asIdeal)
              (Localization.AtPrime (q i).asIdeal)).toNat) ∧
          (∑ i, (Module.length (Localization.AtPrime (q i).asIdeal)
            (Localization.AtPrime (q i).asIdeal)).toNat) ≤ ∏ i, d i := by
  classical
  dsimp only
  let J : Ideal (MvPolynomial σ K) := Ideal.span (Set.range b)
  have hJI : J ≤ I := Ideal.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact hb i)
  have hbJ : ∀ i, b i ∈ J := fun i => Ideal.subset_span (Set.mem_range_self i)
  obtain ⟨hfinite, hdim, hloc, hsum⟩ :=
    pure_power_local_multiplicity_bound K σ J o d b hbJ hu hd
  refine ⟨hfinite, hdim, ?_⟩
  intro ι _ p hp
  let f : (MvPolynomial σ K ⧸ J) →ₐ[K] (MvPolynomial σ K ⧸ I) :=
    Ideal.Quotient.factorₐ K hJI
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hJI
  let q : ι → PrimeSpectrum (MvPolynomial σ K ⧸ J) :=
    fun i => PrimeSpectrum.comap f.toRingHom (p i)
  have hq : Function.Injective q :=
    (PrimeSpectrum.comap_injective_of_surjective f.toRingHom hf).comp hp
  refine ⟨q, hq, ?_, (hsum ι q hq).1⟩
  intro i
  have hle := local_length_le_of_surjective f.toRingHom hf (p i)
  change Module.length (Localization.AtPrime (p i).asIdeal)
      (Localization.AtPrime (p i).asIdeal) ≤
    Module.length (Localization.AtPrime (q i).asIdeal)
      (Localization.AtPrime (q i).asIdeal) at hle
  refine ⟨ne_top_of_le_ne_top (hloc (q i)) hle, hloc (q i), ?_⟩
  exact ENat.toNat_le_toNat hle (hloc (q i))


end TranscendenceTheory

open TranscendenceTheory

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (σ : Type*) [Fintype σ]
    (o : MonomialOrder σ) (d : σ → ℕ) (b : σ → MvPolynomial σ K)
    (hu : ∀ i, IsUnit (o.leadingCoeff (b i)))
    (hd : ∀ i, o.degree (b i) = Finsupp.single i (d i)) :
    let J : Ideal (MvPolynomial σ K) := Ideal.span (Set.range b)
    Module.Finite K (MvPolynomial σ K ⧸ J) ∧
      Module.finrank K (MvPolynomial σ K ⧸ J) ≤ ∏ i, d i ∧
      (∀ p : PrimeSpectrum (MvPolynomial σ K ⧸ J),
        Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal) ≠ ⊤) ∧
      (∀ (ι : Type*) [Fintype ι]
        (p : ι → PrimeSpectrum (MvPolynomial σ K ⧸ J)), Function.Injective p →
        (∑ i, (Module.length (Localization.AtPrime (p i).asIdeal)
          (Localization.AtPrime (p i).asIdeal)).toNat) ≤ ∏ i, d i) ∧
      ∀ (ι : Type*) [Fintype ι] (e : ι → ℕ),
        (∃ I : Ideal (MvPolynomial σ K), (∀ i, b i ∈ I) ∧
          ∃ p : ι → PrimeSpectrum (MvPolynomial σ K ⧸ I),
            Function.Injective p ∧ ∀ i, e i ≤
              (Module.length (Localization.AtPrime (p i).asIdeal)
                (Localization.AtPrime (p i).asIdeal)).toNat) ↔
        ∃ q : ι → PrimeSpectrum (MvPolynomial σ K ⧸ J),
          Function.Injective q ∧ ∀ i, e i ≤
            (Module.length (Localization.AtPrime (q i).asIdeal)
              (Localization.AtPrime (q i).asIdeal)).toNat := by
  classical
  dsimp only
  let J : Ideal (MvPolynomial σ K) := Ideal.span (Set.range b)
  have hbJ : ∀ i, b i ∈ J := fun i => Ideal.subset_span (Set.mem_range_self i)
  obtain ⟨hfinite, hdim, hloc, hsum⟩ :=
    pure_power_local_multiplicity_bound K σ J o d b hbJ hu hd
  refine ⟨hfinite, hdim, hloc, fun ι _ p hp => (hsum ι p hp).1, ?_⟩
  intro ι _ e
  constructor
  · rintro ⟨I, hb, p, hp, he⟩
    obtain ⟨_, _, htransfer⟩ :=
      pure_power_generated_ideal_transfer K σ I o d b hb hu hd
    obtain ⟨q, hq, hle, _⟩ := htransfer ι p hp
    exact ⟨q, hq, fun i => (he i).trans (hle i).2.2⟩
  · rintro ⟨q, hq, he⟩
    exact ⟨J, hbJ, q, hq, he⟩
