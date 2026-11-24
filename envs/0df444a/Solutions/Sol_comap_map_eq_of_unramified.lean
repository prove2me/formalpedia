-- Prove2me | solution 1 for comap_map_eq_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:44:10.75268+00:00
-- url     : https://prove2.me/submissions/c762923e-ad4f-470e-80d9-aae1c6473dfd

module
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Unramified.Locus
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Theorems.Thm_algebraMap_injective_of_isIntegralClosure

set_option autoImplicit false
@[expose] public section
public section
open UniqueFactorizationMonoid Ideal
attribute [local instance] FractionRing.liftAlgebra
variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]
variable {R} {S}
theorem _root_.solution [IsGalois K L] [Algebra.Unramified R S] (I : Ideal S)
    (hI : ∀ σ : L ≃ₐ[K] L, I.comap (galRestrict R K L S σ) = I) :
    (I.comap (algebraMap R S)).map (algebraMap R S) = I := by
  classical
  have : IsDomain S := Function.Injective.isDomain _ (IsIntegralClosure.algebraMap_injective S R L)
  have := IsIntegralClosure.isDedekindDomain R K L S
  have hRS := algebraMap_injective_of_isIntegralClosure K L (R := R) (S := S)
  have := Module.isTorsionFree_iff_algebraMap_injective.mpr hRS
  by_cases hIbot : I = ⊥
  · rw [hIbot, Ideal.comap_bot_of_injective _ hRS, Ideal.map_bot]
  have : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R L
  have hIbot' : I.comap (algebraMap R S) ≠ ⊥ := by
    intro hbot
    apply hIbot
    rw [eq_bot_iff]
    intro x hx
    by_contra hx0
    have hxne : x ≠ 0 := by simpa [Ideal.mem_bot] using hx0
    obtain ⟨p, hp_monic, hp_eval⟩ := Algebra.IsIntegral.isIntegral (R := R) x
    have hex : ∃ n : ℕ, ∃ q : Polynomial R, q ≠ 0 ∧ q.natDegree = n ∧ Polynomial.aeval x q = 0 :=
      ⟨p.natDegree, p, hp_monic.ne_zero, rfl, by simpa [Polynomial.aeval_def] using hp_eval⟩
    obtain ⟨q, hq0, hqdeg, hqeval⟩ := Nat.find_spec hex
    have hc0 : q.coeff 0 ≠ 0 := by
      intro hc
      obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr hc
      have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact hq0 hr
      have hr_eval : Polynomial.aeval x r = 0 := by
        rw [hr, map_mul, Polynomial.aeval_X] at hqeval
        exact (mul_eq_zero.mp hqeval).resolve_left hxne
      have hr_deg : r.natDegree < Nat.find hex := by
        rw [← hqdeg, hr, Polynomial.natDegree_X_mul hr0]; omega
      exact Nat.find_min hex hr_deg ⟨r, hr0, rfl, hr_eval⟩
    have hmem : q.coeff 0 ∈ I.comap (algebraMap R S) := by
      rw [Ideal.mem_comap]
      have hq_eq : q = Polynomial.C (q.coeff 0) + Polynomial.X * q.divX := by
        rw [add_comm]; exact (Polynomial.X_mul_divX_add q).symm
      have h0 := hqeval
      rw [hq_eq, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X] at h0
      have : algebraMap R S (q.coeff 0) = -(x * Polynomial.aeval x q.divX) :=
        eq_neg_of_add_eq_zero_left h0
      rw [this]
      exact I.neg_mem (I.mul_mem_right _ hx)
    rw [hbot, Ideal.mem_bot] at hmem
    exact hc0 hmem
  have : ∀ p, (p.IsPrime ∧ I.comap (algebraMap R S) ≤ p) →
      ∃ P ≥ I, P ∈ primesOver p S := by
    intro p ⟨hp₁, hp₂⟩
    obtain ⟨P, hP1, hP2, hP3⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ _ hp₂
    exact ⟨P, hP1, hP2, ⟨hP3.symm⟩⟩
  choose 𝔓 h𝔓 h𝔓' using this
  suffices I = ∏ p ∈ (factors (I.comap <| algebraMap R S)).toFinset,
    (p.map (algebraMap R S)) ^ (if h : _ then (factors I).count (𝔓 p h) else 0) by
    simp_rw [← Ideal.mapHom_apply, ← map_pow, ← map_prod, Ideal.mapHom_apply] at this
    rw [this, Ideal.map_comap_map]
  conv_lhs => rw [← associated_iff_eq.mp (factors_pow_count_prod hIbot)]
  rw [← Finset.prod_fiberwise_of_maps_to (g := Ideal.comap (algebraMap R S))]
  · apply Finset.prod_congr rfl
    intros p hp
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot'] at hp
    have hpbot : p ≠ ⊥ := fun hp' ↦ hIbot' (eq_bot_iff.mpr (hp.2.trans_eq hp'))
    have : p.IsPrime := hp.1
    have : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hpbot this
    rw [Ideal.map_algebraMap_eq_finsetProd_pow hpbot, ← Finset.prod_pow]
    apply Finset.prod_congr
    · ext P
      rw [factors_eq_normalizedFactors, Finset.mem_filter, Multiset.mem_toFinset,
        Ideal.mem_normalizedFactors_iff hIbot, Set.mem_toFinset]
      refine ⟨fun H ↦ ⟨H.1.1, ⟨H.2.symm⟩⟩, fun H ↦ ⟨⟨H.1, ?_⟩, ?_⟩⟩
      · have ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K L S (h𝔓' _ hp) H
        rw [← hσ, ← hI σ]
        exact Ideal.comap_mono (h𝔓 _ hp)
      · simpa only [Ideal.under_def] using H.2.1.symm
    · intro P hP
      rw [Set.mem_toFinset] at hP
      have : P.IsPrime := hP.1
      have : P.LiesOver p := hP.2
      rw [Ideal.ramificationIdx_eq_one P R, pow_one]
      congr
      rw [dif_pos hp, ← Nat.cast_inj (R := ENat), ← normalize_eq P,
        factors_eq_normalizedFactors,
        ← emultiplicity_eq_count_normalizedFactors
          (prime_of_mem_primesOver hpbot hP).irreducible hIbot,
        ← normalize_eq (𝔓 p hp), ← emultiplicity_eq_count_normalizedFactors
          (prime_of_mem_primesOver hpbot <| h𝔓' p hp).irreducible hIbot,
          emultiplicity_eq_emultiplicity_iff]
      intro n
      have ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K L S (h𝔓' _ hp) hP
      rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le]
      conv_lhs => rw [← hI σ, ← hσ,
        Ideal.comap_le_iff_le_map _ (AlgEquiv.bijective _), Ideal.map_pow,
        Ideal.map_comap_of_surjective _ (AlgEquiv.surjective _)]
  · intro P hP
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot] at hP
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot']
    exact ⟨hP.1.comap _, Ideal.comap_mono hP.2⟩
