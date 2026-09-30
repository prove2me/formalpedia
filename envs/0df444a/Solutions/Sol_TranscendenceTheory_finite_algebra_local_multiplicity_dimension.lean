-- Prove2me | solution 1 for TranscendenceTheory.finite_algebra_local_multiplicity_dimension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T00:36:55.998048+00:00
-- url     : https://prove2.me/submissions/ba493b7e-230a-4078-b5c3-6949e20c12ba

import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Length
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.FieldTheory.IsAlgClosed.Basic

noncomputable section

namespace TranscendenceTheory

theorem finite_local_algebra_length_eq_finrank
    (K A : Type*) [Field K] [IsAlgClosed K] [CommRing A] [IsLocalRing A]
    [Algebra K A] [Module.Finite K A] : Module.length A A = Module.finrank K A := by
  have hres : Function.Surjective (algebraMap K (IsLocalRing.ResidueField A)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral.2
  have hr : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField A) = 1 := by
    rw [← Module.length_eq_of_surjective (R := IsLocalRing.ResidueField K)
      (M := IsLocalRing.ResidueField A) (IsLocalRing.residue_surjective (R := K))]
    rw [Module.length_eq_of_surjective hres]
    simp
  rw [← Module.length_eq_finrank K A, IsLocalRing.length_restrictScalars K A A, hr, mul_one]

theorem finite_algebra_local_length_le_finrank
    (K A : Type*) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (p : PrimeSpectrum A) :
    Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) ≤
      (Module.finrank K (Localization.AtPrime p.asIdeal) : ℕ∞) := by
  let : IsArtinianRing A := IsArtinianRing.of_finite K A
  let : Module.Finite K (Localization.AtPrime p.asIdeal) :=
    Module.Finite.of_surjective
      (Algebra.algHom K A (Localization.AtPrime p.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective p.asIdeal.primeCompl
        (Localization.AtPrime p.asIdeal))
  have h := Submodule.length_le_length_restrictScalars K
      (⊤ : Submodule (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal))
  rw [Module.length_top] at h
  have he := ((Submodule.topEquiv :
    (⊤ : Submodule (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) ≃ₗ[
      Localization.AtPrime p.asIdeal] Localization.AtPrime p.asIdeal).restrictScalars K).length_eq
  exact h.trans_eq (he.trans (Module.length_eq_finrank K _))

/-- Local lengths at distinct primes of a finite algebra have total at most its
vector-space dimension. Finiteness is explicit before conversion to naturals. -/
theorem finite_algebra_local_length_sum_bound
    (K A : Type*) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] :
    (∀ p : PrimeSpectrum A,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) ≠ ⊤) ∧
    ∀ (ι : Type*) [Fintype ι] (p : ι → PrimeSpectrum A), Function.Injective p →
      (∑ i, (Module.length (Localization.AtPrime (p i).asIdeal)
        (Localization.AtPrime (p i).asIdeal)).toNat) ≤ Module.finrank K A := by
  classical
  let : IsArtinianRing A := IsArtinianRing.of_finite K A
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  have hlocal (p : PrimeSpectrum A) := finite_algebra_local_length_le_finrank K A p
  refine ⟨fun p => ne_top_of_le_ne_top (by simp) (hlocal p), ?_⟩
  intro ι _ p hp
  calc
    _ ≤ ∑ i, Module.finrank K (Localization.AtPrime (p i).asIdeal) := by
      apply Finset.sum_le_sum
      intro i _
      simpa using ENat.toNat_le_toNat (hlocal (p i)) (by simp)
    _ = ∑ q ∈ Finset.univ.image p, Module.finrank K (Localization.AtPrime q.asIdeal) := by
      rw [Finset.sum_image]
      exact fun i _ j _ h => hp h
    _ ≤ ∑ q : PrimeSpectrum A, Module.finrank K (Localization.AtPrime q.asIdeal) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = Module.finrank K A := (IsArtinianRing.finrank_eq_sum_primeSpectrum A K).symm

end TranscendenceTheory

open TranscendenceTheory

theorem solution
    (K A : Type*) [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A]
    [Module.Finite K A] :
    (∀ p : PrimeSpectrum A,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) ≠ ⊤) ∧
    ∀ (ι : Type*) [Fintype ι] (p : ι → PrimeSpectrum A), Function.Injective p →
      (∑ i, (Module.length (Localization.AtPrime (p i).asIdeal)
        (Localization.AtPrime (p i).asIdeal)).toNat) ≤ Module.finrank K A ∧
      (Function.Surjective p →
        (∑ i, (Module.length (Localization.AtPrime (p i).asIdeal)
          (Localization.AtPrime (p i).asIdeal)).toNat) = Module.finrank K A) := by
  classical
  let : IsArtinianRing A := IsArtinianRing.of_finite K A
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  obtain ⟨hfinite, hbound⟩ := finite_algebra_local_length_sum_bound K A
  refine ⟨hfinite, fun ι _ p hp => ⟨hbound ι p hp, ?_⟩⟩
  intro hsurj
  have hlocal (q : PrimeSpectrum A) :
      (Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat =
        Module.finrank K (Localization.AtPrime q.asIdeal) := by
    let : Module.Finite K (Localization.AtPrime q.asIdeal) :=
      Module.Finite.of_surjective
        (Algebra.algHom K A (Localization.AtPrime q.asIdeal)).toLinearMap
        (IsArtinianRing.localization_surjective q.asIdeal.primeCompl
          (Localization.AtPrime q.asIdeal))
    rw [finite_local_algebra_length_eq_finrank K, ENat.toNat_natCast]
  simp_rw [hlocal]
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum A K]
  exact (Equiv.ofBijective p ⟨hp, hsurj⟩).sum_comp
    (fun q : PrimeSpectrum A => Module.finrank K (Localization.AtPrime q.asIdeal))
