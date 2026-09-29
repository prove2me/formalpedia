-- Prove2me | solution 1 for ValuationSubring.exists_constantsTower_of_totallyRamified_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a3ee7ff1-8dc7-5b03-9845-69965bb5f560

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_constantsTower_of_totallyRamified_of_isIntegral

set_option autoImplicit false

open IsLocalRing Module

theorem integralClosure_existsUnique_primesOver_of_pow_eq_mul
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra R L] [IsScalarTower R K L]
    (n : ℕ) (hn0 : 0 < n) (hn : finrank K L ≤ n)
    (π : R) (hπ : Irreducible π) (u v : L) (huv : u * v = 1) (hu : IsIntegral R u) (hv : IsIntegral R v)
    (ϖ : L) (hϖ : ϖ ^ n = algebraMap R L π * u) :
    finrank K L = n ∧
    ∃ P : Ideal ↥(integralClosure R L), P.IsMaximal ∧
      (maximalIdeal R).primesOver ↥(integralClosure R L) = {P} ∧
      Ideal.ramificationIdx' (maximalIdeal R) P = n ∧
      Ideal.inertiaDeg' (maximalIdeal R) P = 1 := by
  classical

  haveI : IsIntegralClosure ↥(integralClosure R L) R L := integralClosure.isIntegralClosure R L
  haveI hDed : IsDedekindDomain ↥(integralClosure R L) := IsIntegralClosure.isDedekindDomain R K L ↥(integralClosure R L)
  haveI hFin : Module.Finite R ↥(integralClosure R L) := IsIntegralClosure.finite R K L ↥(integralClosure R L)
  haveI : IsFractionRing ↥(integralClosure R L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R K L ↥(integralClosure R L)
  set S := integralClosure R L with hSdef
  set p := maximalIdeal R with hpdef
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have hpπ : p = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ

  have hint : IsIntegral R ϖ := by
    refine IsIntegral.of_pow hn0 ?_
    rw [hϖ]; exact isIntegral_algebraMap.mul hu
  set ϖS : ↥S := ⟨ϖ, hint⟩ with hϖS
  set uS : ↥S := ⟨u, hu⟩ with huSdef
  have huS : IsUnit uS := isUnit_iff_exists_inv.mpr ⟨⟨v, hv⟩, Subtype.ext huv⟩
  have hu0 : u ≠ 0 := fun h => by rw [h, zero_mul] at huv; exact zero_ne_one huv
  have hπS : algebraMap R ↥S π * uS = ϖS ^ n := by
    apply Subtype.ext
    show algebraMap R L π * u = ϖ ^ n
    rw [hϖ]
  have hmap : Ideal.map (algebraMap R ↥S) p = (Ideal.span {ϖS}) ^ n := by
    rw [hpπ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
    apply Ideal.span_singleton_eq_span_singleton.mpr
    rw [← hπS]
    exact associated_mul_unit_right _ _ huS
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have hϖ0 : ϖS ≠ 0 := by
    intro h0
    have h1 : ϖ = 0 := congrArg Subtype.val h0
    have h2 : algebraMap R L π * u = 0 := by rw [← hϖ, h1, zero_pow hn0.ne']
    rcases mul_eq_zero.mp h2 with h | h
    · exact hπ.ne_zero (hRL (by rw [h, map_zero]))
    · exact hu0 h
  have hspan0 : Ideal.span {ϖS} ≠ ⊥ := by rwa [ne_eq, Ideal.span_singleton_eq_bot]
  have hmap0 : Ideal.map (algebraMap R ↥S) p ≠ ⊥ := by rw [hmap]; exact pow_ne_zero _ hspan0
  haveI : Module.IsTorsionFree R L :=
    ⟨fun r hr x y hxy => by
      have h0 : algebraMap R L r ≠ 0 := fun h => hr.ne_zero (hRL (by rw [h, map_zero]))
      simp only [Algebra.smul_def] at hxy
      exact mul_left_cancel₀ h0 hxy⟩
  haveI : Module.IsTorsionFree R ↥S := Subalgebra.instIsTorsionFree _

  have hprime_over : ∀ P ∈ IsDedekindDomain.primesOverFinset p ↥S, P.IsPrime ∧ P.LiesOver p := fun P hP =>
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 ↥S).mp hP
  have he : ∀ P ∈ IsDedekindDomain.primesOverFinset p ↥S, n ≤ Ideal.ramificationIdx' p P := by
    intro P hP
    obtain ⟨hPp, hPo⟩ := hprime_over P hP
    have hdvd : P ∣ Ideal.map (algebraMap R ↥S) p := Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr hPo.over.le)
    have hP0 : P ≠ ⊥ := by
      rintro rfl
      exact hmap0 (le_bot_iff.mp (Ideal.le_of_dvd hdvd))
    have hPpr : Prime P := Ideal.prime_of_isPrime hP0 hPp
    rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0 hPp hP0, hmap,
      UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]
    have hdvd1 : P ∣ Ideal.span {ϖS} := hPpr.dvd_of_dvd_pow (by rw [← hmap]; exact hdvd)
    obtain ⟨Q, hQ, hPQ⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hspan0 hPpr.irreducible hdvd1
    rw [associated_iff_eq] at hPQ
    subst hPQ
    have : 1 ≤ (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {ϖS})).count P := Multiset.one_le_count_iff_mem.mpr hQ
    calc n = n * 1 := (mul_one n).symm
      _ ≤ n * _ := Nat.mul_le_mul_left n this
  have hf : ∀ P ∈ IsDedekindDomain.primesOverFinset p ↥S, 1 ≤ Ideal.inertiaDeg' p P := by
    intro P hP
    obtain ⟨hPp, hPo⟩ := hprime_over P hP
    haveI := hPp; haveI := hPo
    exact Ideal.inertiaDeg'_pos p P

  have hsum := Ideal.sum_ramification_inertia ↥S K L hp0
  have hne : (IsDedekindDomain.primesOverFinset p ↥S).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsum
    exact (Module.finrank_pos (R := K) (M := L)).ne' hsum.symm
  have hcard : (IsDedekindDomain.primesOverFinset p ↥S).card * n ≤ n := by
    calc (IsDedekindDomain.primesOverFinset p ↥S).card * n
        = ∑ P ∈ IsDedekindDomain.primesOverFinset p ↥S, n := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset p ↥S, Ideal.ramificationIdx' p P * Ideal.inertiaDeg' p P :=
          Finset.sum_le_sum fun P hP => by nlinarith [he P hP, hf P hP]
      _ = finrank K L := hsum
      _ ≤ n := hn
  have hcard1 : (IsDedekindDomain.primesOverFinset p ↥S).card = 1 := by
    have h1 : (IsDedekindDomain.primesOverFinset p ↥S).card ≤ 1 := by
      by_contra h; push Not at h
      have : 2 * n ≤ (IsDedekindDomain.primesOverFinset p ↥S).card * n := Nat.mul_le_mul_right n h
      omega
    have h2 := Finset.card_pos.mpr hne
    omega
  obtain ⟨P, hPeq⟩ := Finset.card_eq_one.mp hcard1
  have hPmem : P ∈ IsDedekindDomain.primesOverFinset p ↥S := by rw [hPeq]; exact Finset.mem_singleton_self P
  obtain ⟨hPp, hPo⟩ := hprime_over P hPmem
  have heP := he P hPmem
  have hfP := hf P hPmem
  rw [hPeq, Finset.sum_singleton] at hsum
  have hef : Ideal.ramificationIdx' p P * Ideal.inertiaDeg' p P ≤ n := hsum ▸ hn
  have hfP1 : Ideal.inertiaDeg' p P = 1 := by
    by_contra h
    have h2 : 2 ≤ Ideal.inertiaDeg' p P := by omega
    have : 2 * n ≤ Ideal.ramificationIdx' p P * Ideal.inertiaDeg' p P := by nlinarith
    omega
  have heP' : Ideal.ramificationIdx' p P = n := by
    rw [hfP1, mul_one] at hef; omega
  have hfin : finrank K L = n := by rw [← hsum, hfP1, mul_one, heP']
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hmap0 (le_bot_iff.mp (Ideal.map_le_iff_le_comap.mpr hPo.over.le))
  haveI := hPp
  refine ⟨hfin, P, Ideal.IsPrime.isMaximal hPp hP0, ?_, heP', hfP1⟩
  rw [← IsDedekindDomain.coe_primesOverFinset hp0 ↥S, hPeq, Finset.coe_singleton]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem existsUnique_valuationSubring_of_pow_eq_mul
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra R L] [IsScalarTower R K L]
    (n : ℕ) (hn0 : 0 < n) (hn : finrank K L ≤ n)
    (π : R) (hπ : Irreducible π) (u v : L) (huv : u * v = 1) (hu : IsIntegral R u) (hv : IsIntegral R v)
    (ϖ : L) (hϖ : ϖ ^ n = algebraMap R L π * u) :
    finrank K L = n ∧
    ∃ (W : ValuationSubring L) (hRW : ∀ r : R, algebraMap R L r ∈ W),
      (∀ r ∈ maximalIdeal R, (⟨algebraMap R L r, hRW r⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      IsDiscreteValuationRing ↥W ∧
      (∃ hϖW : ϖ ∈ W, maximalIdeal ↥W = Ideal.span {(⟨ϖ, hϖW⟩ : ↥W)}) ∧
      (∀ w : ↥W, ∃ r : R, w - ⟨algebraMap R L r, hRW r⟩ ∈ maximalIdeal ↥W) ∧
      (∀ k : K, algebraMap K L k ∈ W ↔ ∃ r : R, algebraMap R K r = k) ∧
      (∀ (W' : ValuationSubring L) (hRW' : ∀ r : R, algebraMap R L r ∈ W'),
        (∀ r ∈ maximalIdeal R, (⟨algebraMap R L r, hRW' r⟩ : ↥W') ∈ maximalIdeal ↥W') → W' = W) := by
  classical
  obtain ⟨hfin, P, hPmax, hPover, heP, hfP⟩ :=
    integralClosure_existsUnique_primesOver_of_pow_eq_mul R K L n hn0 hn π hπ u v huv hu hv ϖ hϖ
  haveI : IsIntegralClosure ↥(integralClosure R L) R L := integralClosure.isIntegralClosure R L
  haveI hDed : IsDedekindDomain ↥(integralClosure R L) := IsIntegralClosure.isDedekindDomain R K L ↥(integralClosure R L)
  haveI hFin : Module.Finite R ↥(integralClosure R L) := IsIntegralClosure.finite R K L ↥(integralClosure R L)
  haveI : IsFractionRing ↥(integralClosure R L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R K L ↥(integralClosure R L)
  haveI := hPmax
  haveI hPprime : P.IsPrime := hPmax.isPrime
  have hp0 : maximalIdeal R ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have hPmem : P ∈ (maximalIdeal R).primesOver ↥(integralClosure R L) := by rw [hPover]; exact Set.mem_singleton P
  haveI hPo : P.LiesOver (maximalIdeal R) := hPmem.2
  have hP0 : P ≠ ⊥ := by
    intro h
    have : Ideal.map (algebraMap R ↥(integralClosure R L)) (maximalIdeal R) ≤ P := Ideal.map_le_iff_le_comap.mpr hPo.over.le
    rw [h, le_bot_iff, Ideal.map_eq_bot_iff_of_injective] at this
    · exact hp0 this
    · intro a b hab
      exact hRL (congrArg Subtype.val hab)

  haveI : IsDomain (Localization.AtPrime P) := IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
  have hSL : Function.Injective (algebraMap ↥(integralClosure R L) L) := Subtype.val_injective
  have hunits : ∀ y : P.primeCompl, IsUnit (algebraMap ↥(integralClosure R L) L y) := by
    intro y
    apply IsUnit.mk0
    intro h0
    have hy0 : (y : ↥(integralClosure R L)) = 0 := hSL (by rw [h0]; simp)
    exact y.2 (by rw [hy0]; exact P.zero_mem)
  letI algAL : Algebra (Localization.AtPrime P) L := (IsLocalization.lift (M := P.primeCompl) hunits).toAlgebra
  have halgAL : ∀ s : ↥(integralClosure R L), algebraMap (Localization.AtPrime P) L (algebraMap ↥(integralClosure R L) (Localization.AtPrime P) s) = (s : L) :=
    fun s => IsLocalization.lift_eq hunits s
  haveI : IsScalarTower ↥(integralClosure R L) (Localization.AtPrime P) L := IsScalarTower.of_algebraMap_eq fun s => (halgAL s).symm
  haveI : IsFractionRing (Localization.AtPrime P) L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl (Localization.AtPrime P) L
  have hAL : Function.Injective (algebraMap (Localization.AtPrime P) L) := IsFractionRing.injective (Localization.AtPrime P) L
  haveI hDVRA : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ↥(integralClosure R L) hP0 (Localization.AtPrime P)

  set W : ValuationSubring L := (ValuationRing.valuation (Localization.AtPrime P) L).valuationSubring with hWdef
  have hmemW : ∀ x : L, x ∈ W ↔ ∃ a : Localization.AtPrime P, algebraMap (Localization.AtPrime P) L a = x := by
    intro x
    rw [hWdef, Valuation.mem_valuationSubring_iff, ← Valuation.mem_integer_iff]
    exact ValuationRing.mem_integer_iff (Localization.AtPrime P) L x
  let f : Localization.AtPrime P →+* ↥W :=
    { toFun := fun a => ⟨algebraMap (Localization.AtPrime P) L a, (hmemW _).mpr ⟨a, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b) }
  have hf_apply : ∀ a, ((f a : ↥W) : L) = algebraMap (Localization.AtPrime P) L a := fun a => rfl
  have hfbij : Function.Bijective f := by
    refine ⟨fun a b hab => hAL (by rw [← hf_apply, ← hf_apply, hab]), fun w => ?_⟩
    obtain ⟨a, ha⟩ := (hmemW (w : L)).mp w.2
    exact ⟨a, Subtype.ext ha⟩
  let eAW : Localization.AtPrime P ≃+* ↥W := RingEquiv.ofBijective f hfbij
  have heAW : ∀ a, ((eAW a : ↥W) : L) = algebraMap (Localization.AtPrime P) L a := fun a => rfl
  have hSW : ∀ s : ↥(integralClosure R L), (s : L) ∈ W := fun s => (hmemW _).mpr ⟨algebraMap ↥(integralClosure R L) _ s, halgAL s⟩
  have heAWS : ∀ s : ↥(integralClosure R L), eAW (algebraMap ↥(integralClosure R L) (Localization.AtPrime P) s) = ⟨(s : L), hSW s⟩ :=
    fun s => Subtype.ext (by rw [heAW, halgAL])
  have hRW : ∀ r : R, algebraMap R L r ∈ W := fun r => by
    have : algebraMap R L r = ((algebraMap R ↥(integralClosure R L) r : ↥(integralClosure R L)) : L) := rfl
    rw [this]; exact hSW _

  haveI : IsPrincipalIdealRing ↥W := IsPrincipalIdealRing.of_surjective (eAW : Localization.AtPrime P →+* ↥W) eAW.surjective
  have hunitW : ∀ a : Localization.AtPrime P, IsUnit (eAW a) ↔ IsUnit a :=
    fun a => ⟨fun h => by simpa using h.map eAW.symm, fun h => h.map eAW⟩
  have hmemmaxW : ∀ a : Localization.AtPrime P, eAW a ∈ maximalIdeal ↥W ↔ a ∈ maximalIdeal (Localization.AtPrime P) := by
    intro a; rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, hunitW]
  have hSmax : ∀ s : ↥(integralClosure R L), (⟨(s : L), hSW s⟩ : ↥W) ∈ maximalIdeal ↥W ↔ s ∈ P := by
    intro s
    rw [← heAWS, hmemmaxW]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P s

  have hcentre : ∀ r ∈ maximalIdeal R, (⟨algebraMap R L r, hRW r⟩ : ↥W) ∈ maximalIdeal ↥W := by
    intro r hr
    have : (⟨algebraMap R L r, hRW r⟩ : ↥W) = ⟨((algebraMap R ↥(integralClosure R L) r : ↥(integralClosure R L)) : L), hSW _⟩ := rfl
    rw [this, hSmax]
    exact hPo.over.le hr |> fun h => (Ideal.mem_comap.mp h)

  have hπW : (⟨algebraMap R L π, hRW π⟩ : ↥W) ∈ maximalIdeal ↥W :=
    hcentre π ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ ▸ Ideal.mem_span_singleton_self π)
  have hπW0 : (⟨algebraMap R L π, hRW π⟩ : ↥W) ≠ 0 := by
    intro h
    exact hπ.ne_zero (hRL (by rw [map_zero]; exact congrArg Subtype.val h))
  have hDVRW : IsDiscreteValuationRing ↥W :=
    { toIsPrincipalIdealRing := inferInstance
      toIsLocalRing := inferInstance
      not_a_field' := by
        intro hbot
        have := hπW
        rw [hbot, Ideal.mem_bot] at this
        exact hπW0 this }

  have hresK : ∀ k : K, algebraMap K L k ∈ W ↔ ∃ r : R, algebraMap R K r = k := by
    intro k
    constructor
    · intro hk
      rcases ValuationRing.isInteger_or_isInteger R k with ⟨r, hr⟩ | ⟨r, hr⟩
      · exact ⟨r, hr⟩
      · by_cases hk0 : k = 0
        · exact ⟨0, by rw [hk0, map_zero]⟩
        by_cases hru : IsUnit r
        · obtain ⟨v, rfl⟩ := hru
          refine ⟨((v⁻¹ : Rˣ) : R), ?_⟩
          have h1 : algebraMap R K ((v⁻¹ : Rˣ) : R) * algebraMap R K (v : R) = 1 := by
            rw [← map_mul, Units.inv_mul, map_one]
          rw [hr] at h1
          calc algebraMap R K ((v⁻¹ : Rˣ) : R) = algebraMap R K ((v⁻¹ : Rˣ) : R) * (k⁻¹ * k) := by
                rw [inv_mul_cancel₀ hk0, mul_one]
            _ = k := by rw [← mul_assoc, h1, one_mul]
        · exfalso
          have hrm : r ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hru
          have h1 : (⟨algebraMap R L r, hRW r⟩ : ↥W) ∈ maximalIdeal ↥W := hcentre r hrm
          have h2 : algebraMap R L r * algebraMap K L k = 1 := by
            rw [IsScalarTower.algebraMap_apply R K L, hr, ← map_mul, inv_mul_cancel₀ hk0, map_one]
          have hunit : IsUnit (⟨algebraMap R L r, hRW r⟩ : ↥W) :=
            isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K L k, hk⟩, Subtype.ext h2⟩
          exact (IsLocalRing.mem_maximalIdeal _).mp h1 hunit
    · rintro ⟨r, rfl⟩
      rw [← IsScalarTower.algebraMap_apply]
      exact hRW r

  have hmemWfrac : ∀ x : L, x ∈ W ↔ ∃ (s : ↥(integralClosure R L)) (t : ↥(integralClosure R L)), t ∉ P ∧ x * (t : L) = (s : L) := by
    intro x
    rw [hmemW]
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl a
      refine ⟨s, t, t.2, ?_⟩
      rw [← halgAL t, ← map_mul, IsLocalization.mk'_spec, halgAL]
    · rintro ⟨s, t, ht, hx⟩
      refine ⟨IsLocalization.mk' _ s (⟨t, ht⟩ : P.primeCompl), ?_⟩
      have ht0 : (t : L) ≠ 0 := fun h => ht (by rw [show t = 0 from Subtype.ext h]; exact P.zero_mem)
      apply mul_right_cancel₀ ht0
      rw [hx, ← halgAL t, ← map_mul]
      show algebraMap _ L (IsLocalization.mk' (Localization.AtPrime P) s (⟨t, ht⟩ : P.primeCompl) * algebraMap _ _ ((⟨t, ht⟩ : P.primeCompl) : ↥(integralClosure R L))) = _
      rw [IsLocalization.mk'_spec, halgAL]
  have huniq : ∀ (W' : ValuationSubring L) (hRW' : ∀ r : R, algebraMap R L r ∈ W'),
      (∀ r ∈ maximalIdeal R, (⟨algebraMap R L r, hRW' r⟩ : ↥W') ∈ maximalIdeal ↥W') → W' = W := by
    intro W' hRW' hcen'

    have hSW' : ∀ s : ↥(integralClosure R L), (s : L) ∈ W' := by
      intro s
      have hsint : IsIntegral R (s : L) := s.2
      letI : Algebra R ↥W' := ((algebraMap R L).codRestrict W'.toSubring hRW').toAlgebra
      haveI : IsScalarTower R ↥W' L := IsScalarTower.of_algebraMap_eq fun r => rfl
      have hsint' : IsIntegral ↥W' (s : L) := hsint.tower_top
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥W') (K := L)).mp hsint'
      rw [← hy]; exact y.2

    let ι' : ↥(integralClosure R L) →+* ↥W' := (integralClosure R L).val.toRingHom.codRestrict W'.toSubring hSW'
    let Q : Ideal ↥(integralClosure R L) := (maximalIdeal ↥W').comap ι'
    have hQmem : ∀ s : ↥(integralClosure R L), s ∈ Q ↔ (⟨(s : L), hSW' s⟩ : ↥W') ∈ maximalIdeal ↥W' := fun s => Iff.rfl
    haveI hQprime : Q.IsPrime := Ideal.comap_isPrime _ _
    have hQne : Q.comap (algebraMap R ↥(integralClosure R L)) ≠ ⊤ := by
      rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_comap, map_one, hQmem]
      intro h1
      exact (IsLocalRing.mem_maximalIdeal _).mp h1 ⟨⟨⟨_, hSW' 1⟩, ⟨_, hSW' 1⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩, rfl⟩
    have hQle : maximalIdeal R ≤ Q.comap (algebraMap R ↥(integralClosure R L)) := by
      intro r hr
      rw [Ideal.mem_comap, hQmem]
      exact hcen' r hr
    haveI hQover : Q.LiesOver (maximalIdeal R) := ⟨(IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hQne hQle⟩
    have hQP : Q = P := by
      have : Q ∈ (maximalIdeal R).primesOver ↥(integralClosure R L) := ⟨hQprime, hQover⟩
      rw [hPover] at this
      exact this

    have hWW' : W ≤ W' := by
      intro x hx
      obtain ⟨s, t, ht, hxt⟩ := (hmemWfrac x).mp hx
      have htQ : t ∉ Q := by rw [hQP]; exact ht
      have htunit : IsUnit (⟨(t : L), hSW' t⟩ : ↥W') := by
        by_contra h
        exact htQ ((hQmem t).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h))
      have ht0 : (t : L) ≠ 0 := fun h => ht (by rw [show t = 0 from Subtype.ext h]; exact P.zero_mem)
      have hx' : x = (s : L) * (t : L)⁻¹ := by rw [← hxt, mul_inv_cancel_right₀ ht0]
      rw [hx']
      refine mul_mem (hSW' s) ?_
      have hv : W'.valuation (t : L) = 1 := (W'.valuation_eq_one_iff ⟨(t : L), hSW' t⟩).mp htunit
      apply (W'.valuation_le_one_iff _).mp
      rw [map_inv₀, hv, inv_one]

    set J := W.idealOfLE W' hWW' with hJdef
    have hJmem : ∀ w : ↥W, w ∈ J ↔ (⟨(w : L), hWW' w.2⟩ : ↥W') ∈ maximalIdeal ↥W' := fun w => Iff.rfl
    haveI : J.IsPrime := ValuationSubring.prime_idealOfLE W W' hWW'
    have hJ0 : J ≠ ⊥ := by
      intro hJ0
      have hπJ : (⟨algebraMap R L π, hRW π⟩ : ↥W) ∈ J := by
        rw [hJmem]
        exact hcen' π ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ ▸ Ideal.mem_span_singleton_self π)
      rw [hJ0, Ideal.mem_bot] at hπJ
      exact hπW0 hπJ
    have hJmax : J = maximalIdeal ↥W := IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hJ0)
    apply le_antisymm _ hWW'
    intro x hx'
    by_contra hxW
    have hxinv : x⁻¹ ∈ W := (W.mem_or_inv_mem x).resolve_left hxW
    have hx0 : x ≠ 0 := fun h => hxW (h ▸ W.zero_mem)

    have hxm : (⟨x⁻¹, hxinv⟩ : ↥W) ∈ maximalIdeal ↥W := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
      have hb' : x⁻¹ * (b : L) = 1 := congrArg Subtype.val hb
      have : (b : L) = x := by
        have := congrArg (fun z => x * z) hb'
        simp only [← mul_assoc, mul_inv_cancel₀ hx0, one_mul, mul_one] at this
        exact this
      exact hxW (this ▸ b.2)
    rw [← hJmax, hJmem] at hxm
    have hu' : IsUnit (⟨x⁻¹, hWW' hxinv⟩ : ↥W') :=
      isUnit_iff_exists_inv.mpr ⟨⟨x, hx'⟩, Subtype.ext (inv_mul_cancel₀ hx0)⟩
    exact (IsLocalRing.mem_maximalIdeal _).mp hxm hu'

  have hint : IsIntegral R ϖ := by
    refine IsIntegral.of_pow hn0 ?_
    rw [hϖ]; exact isIntegral_algebraMap.mul hu
  set ϖS : ↥(integralClosure R L) := ⟨ϖ, hint⟩ with hϖS
  set uS : ↥(integralClosure R L) := ⟨u, hu⟩ with huSdef
  have huS : IsUnit uS := isUnit_iff_exists_inv.mpr ⟨⟨v, hv⟩, Subtype.ext huv⟩
  have hu0 : u ≠ 0 := fun h => by rw [h, zero_mul] at huv; exact zero_ne_one huv
  have hπS : algebraMap R ↥(integralClosure R L) π * uS = ϖS ^ n := by
    apply Subtype.ext
    show algebraMap R L π * u = ϖ ^ n
    rw [hϖ]
  have hmap : Ideal.map (algebraMap R ↥(integralClosure R L)) (maximalIdeal R) = (Ideal.span {ϖS}) ^ n := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
    apply Ideal.span_singleton_eq_span_singleton.mpr
    rw [← hπS]
    exact associated_mul_unit_right _ _ huS
  have hϖ0 : ϖS ≠ 0 := by
    intro h0
    have h1 : ϖ = 0 := congrArg Subtype.val h0
    have h2 : algebraMap R L π * u = 0 := by rw [← hϖ, h1, zero_pow hn0.ne']
    rcases mul_eq_zero.mp h2 with h | h
    · exact hπ.ne_zero (hRL (by rw [h, map_zero]))
    · exact hu0 h
  have hspan0 : Ideal.span {ϖS} ≠ ⊥ := by rwa [ne_eq, Ideal.span_singleton_eq_bot]
  have hmap0 : Ideal.map (algebraMap R ↥(integralClosure R L)) (maximalIdeal R) ≠ ⊥ := by rw [hmap]; exact pow_ne_zero _ hspan0
  have hPpr : Prime P := Ideal.prime_of_isPrime hP0 hPprime
  have hdvdP : P ∣ Ideal.map (algebraMap R ↥(integralClosure R L)) (maximalIdeal R) :=
    Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr hPo.over.le)

  have hfac : ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {ϖS}), Q = P := by
    intro Q hQ
    have hQpr : Prime Q := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
    have hQdvd : Q ∣ Ideal.map (algebraMap R ↥(integralClosure R L)) (maximalIdeal R) := by
      rw [hmap]; exact dvd_pow (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ) hn0.ne'
    have hQ0 : Q ≠ ⊥ := hQpr.ne_zero
    haveI hQprime : Q.IsPrime := Ideal.isPrime_of_prime hQpr
    have hQle : Ideal.map (algebraMap R ↥(integralClosure R L)) (maximalIdeal R) ≤ Q := Ideal.le_of_dvd hQdvd
    have hQne : Q.comap (algebraMap R ↥(integralClosure R L)) ≠ ⊤ := by
      rw [Ne, Ideal.comap_eq_top_iff]; exact hQprime.ne_top
    haveI : Q.LiesOver (maximalIdeal R) :=
      ⟨(IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hQne (Ideal.map_le_iff_le_comap.mp hQle)⟩
    have : Q ∈ (maximalIdeal R).primesOver ↥(integralClosure R L) := ⟨hQprime, inferInstance⟩
    rw [hPover] at this
    exact this
  have hcount : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {ϖS})).count P = 1 := by
    have h1 := heP
    rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0 hPprime hP0, hmap,
      UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul] at h1
    have : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {ϖS})).count P * n = 1 * n := by rw [one_mul, mul_comm]; exact h1
    exact Nat.eq_of_mul_eq_mul_right hn0 this
  have hnf : UniqueFactorizationMonoid.normalizedFactors (Ideal.span {ϖS}) = {P} := by
    have hrep := Multiset.eq_replicate_of_mem hfac
    rw [hrep, Multiset.count_replicate_self] at hcount
    rw [hrep, hcount, Multiset.replicate_one]
  have hspanP : Ideal.span {ϖS} = P := by
    have hassoc := UniqueFactorizationMonoid.prod_normalizedFactors hspan0
    rw [hnf, Multiset.prod_singleton] at hassoc
    exact (associated_iff_eq.mp hassoc).symm
  have hϖW : ϖ ∈ W := hSW ϖS
  have hmaxW : maximalIdeal ↥W = Ideal.span {(⟨ϖ, hϖW⟩ : ↥W)} := by
    have hmaxA : maximalIdeal (Localization.AtPrime P) = Ideal.span {algebraMap ↥(integralClosure R L) (Localization.AtPrime P) ϖS} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal,
        ← congrArg (Ideal.map (algebraMap ↥(integralClosure R L) (Localization.AtPrime P))) hspanP,
        Ideal.map_span, Set.image_singleton]
    apply le_antisymm
    · intro w hw
      have h1 : eAW.symm w ∈ maximalIdeal (Localization.AtPrime P) := by
        rw [← hmemmaxW, RingEquiv.apply_symm_apply]; exact hw
      rw [hmaxA, Ideal.mem_span_singleton] at h1
      obtain ⟨c, hc⟩ := h1
      rw [Ideal.mem_span_singleton]
      refine ⟨eAW c, ?_⟩
      have : w = eAW (eAW.symm w) := (RingEquiv.apply_symm_apply eAW w).symm
      rw [this, hc, map_mul, heAWS]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show (⟨ϖ, hϖW⟩ : ↥W) ∈ maximalIdeal ↥W
      have : (⟨ϖ, hϖW⟩ : ↥W) = ⟨((ϖS : ↥(integralClosure R L)) : L), hSW ϖS⟩ := rfl
      rw [this, hSmax, ← hspanP]
      exact Ideal.mem_span_singleton_self ϖS

  have hresS : ∀ s : ↥(integralClosure R L), ∃ r : R, s - algebraMap R _ r ∈ P := by
    intro s
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    have hf1 : Module.finrank (R ⧸ maximalIdeal R) (↥(integralClosure R L) ⧸ P) = 1 := by
      rw [← Ideal.inertiaDeg_algebraMap]; exact hfP
    have h1 : (1 : ↥(integralClosure R L) ⧸ P) ≠ 0 := by
      rw [Ne, ← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
      exact hPprime.ne_top ∘ (Ideal.eq_top_iff_one P).mpr
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := R ⧸ maximalIdeal R) (1 : ↥(integralClosure R L) ⧸ P) h1).mp hf1 (Ideal.Quotient.mk P s)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨r, ?_⟩
    rw [← Ideal.Quotient.eq, ← hc, Algebra.smul_def, mul_one]
    rfl
  have hres : ∀ w : ↥W, ∃ r : R, w - ⟨algebraMap R L r, hRW r⟩ ∈ maximalIdeal ↥W := by
    intro w
    obtain ⟨s, t, ht, hwt⟩ := (hmemWfrac (w : L)).mp w.2
    obtain ⟨rt, hrt⟩ := hresS t
    obtain ⟨rs, hrs⟩ := hresS s
    have hrtu : IsUnit rt := by
      by_contra h
      have hrtm : algebraMap R ↥(integralClosure R L) rt ∈ P := hPo.over.le ((IsLocalRing.mem_maximalIdeal _).mpr h)
      exact ht (by simpa using P.add_mem hrt hrtm)
    obtain ⟨v, hv⟩ := hrtu
    refine ⟨rs * ((v⁻¹ : Rˣ) : R), ?_⟩

    have ht0 : (t : L) ≠ 0 := fun h => ht (by rw [show t = 0 from Subtype.ext h]; exact P.zero_mem)
    have htunitW : IsUnit (⟨(t : L), hSW t⟩ : ↥W) := by
      by_contra h
      exact ht ((hSmax t).mp ((IsLocalRing.mem_maximalIdeal _).mpr h))
    have hvv : algebraMap R ↥(integralClosure R L) (v : R) * algebraMap R ↥(integralClosure R L) ((v⁻¹ : Rˣ) : R) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hnum : s - t * algebraMap R _ (rs * ((v⁻¹ : Rˣ) : R)) ∈ P := by
      have e1 : s - t * algebraMap R _ (rs * ((v⁻¹ : Rˣ) : R)) =
          (s - algebraMap R _ rs) - (t - algebraMap R _ rt) * algebraMap R _ (rs * ((v⁻¹ : Rˣ) : R)) := by
        rw [← hv, map_mul]
        linear_combination (-(algebraMap R ↥(integralClosure R L) rs)) * hvv
      rw [e1]
      exact P.sub_mem hrs (P.mul_mem_right _ hrt)
    have hprod : (w - ⟨algebraMap R L (rs * ((v⁻¹ : Rˣ) : R)), hRW _⟩) * ⟨(t : L), hSW t⟩ =
        (⟨((s - t * algebraMap R ↥(integralClosure R L) (rs * ((v⁻¹ : Rˣ) : R)) : ↥(integralClosure R L)) : L), hSW _⟩ : ↥W) := by
      apply Subtype.ext
      show ((w : L) - algebraMap R L (rs * ((v⁻¹ : Rˣ) : R))) * (t : L) = _
      rw [sub_mul, hwt]
      push_cast
      simp only [Algebra.cast, map_mul]
      ring
    have hmem : (w - ⟨algebraMap R L (rs * ((v⁻¹ : Rˣ) : R)), hRW _⟩) * ⟨(t : L), hSW t⟩ ∈ maximalIdeal ↥W := by
      rw [hprod, hSmax]; exact hnum
    exact (Ideal.mul_unit_mem_iff_mem _ htunitW).mp hmem
  exact ⟨hfin, W, hRW, hcentre, hDVRW, ⟨hϖW, hmaxW⟩, hres, hresK, huniq⟩

section Layer

variable {k F : Type*} [Field k] [CharZero k] [Field F] [Algebra k F]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in

theorem layer_existsUnique_valuationSubring
    (F₀ : IntermediateField k F) (W₀ : ValuationSubring ↥F₀) (hdvr : IsDiscreteValuationRing ↥W₀)
    (π₀ : k) (hπ₀ : algebraMap k ↥F₀ π₀ ∈ W₀)
    (hunif : maximalIdeal ↥W₀ = Ideal.span {(⟨algebraMap k ↥F₀ π₀, hπ₀⟩ : ↥W₀)})
    (n : ℕ) (hn0 : 0 < n) (ϖ : F) (hϖint : IsIntegral k ϖ) (hdeg : (minpoly k ϖ).natDegree = n)
    (u v : F) (huv : u * v = 1)
    (pu : Polynomial k) (hpu : pu.Monic) (hpuc : ∀ i, algebraMap k ↥F₀ (pu.coeff i) ∈ W₀) (hpu0 : Polynomial.aeval u pu = 0)
    (pv : Polynomial k) (hpv : pv.Monic) (hpvc : ∀ i, algebraMap k ↥F₀ (pv.coeff i) ∈ W₀) (hpv0 : Polynomial.aeval v pv = 0)
    (hϖ : ϖ ^ n = algebraMap k F π₀ * u) :
    let E : IntermediateField ↥F₀ F := IntermediateField.adjoin ↥F₀ {ϖ}
    Module.finrank ↥F₀ ↥E = n ∧
    ∃ (W : ValuationSubring ↥E) (hRW : ∀ r : ↥W₀, algebraMap ↥F₀ ↥E r ∈ W),
      (∀ r ∈ maximalIdeal ↥W₀, (⟨algebraMap ↥F₀ ↥E r, hRW r⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      IsDiscreteValuationRing ↥W ∧
      (∃ hϖW : (⟨ϖ, IntermediateField.mem_adjoin_simple_self ↥F₀ ϖ⟩ : ↥E) ∈ W,
        maximalIdeal ↥W = Ideal.span {(⟨_, hϖW⟩ : ↥W)}) ∧
      (∀ w : ↥W, ∃ r : ↥W₀, w - ⟨algebraMap ↥F₀ ↥E r, hRW r⟩ ∈ maximalIdeal ↥W) ∧
      (∀ f : ↥F₀, algebraMap ↥F₀ ↥E f ∈ W ↔ ∃ r : ↥W₀, (r : ↥F₀) = f) ∧
      (∀ (W' : ValuationSubring ↥E) (hRW' : ∀ r : ↥W₀, algebraMap ↥F₀ ↥E r ∈ W'),
        (∀ r ∈ maximalIdeal ↥W₀, (⟨algebraMap ↥F₀ ↥E r, hRW' r⟩ : ↥W') ∈ maximalIdeal ↥W') → W' = W) := by
  intro E
  haveI : CharZero ↥F₀ := charZero_of_injective_algebraMap (algebraMap k ↥F₀).injective
  haveI : PerfectField ↥F₀ := PerfectField.ofCharZero
  have hϖF₀ : IsIntegral ↥F₀ ϖ := hϖint.tower_top
  haveI : FiniteDimensional ↥F₀ ↥E := IntermediateField.adjoin.finiteDimensional hϖF₀
  haveI : Algebra.IsSeparable ↥F₀ ↥E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  letI algWE : Algebra ↥W₀ ↥E := ((algebraMap ↥F₀ ↥E).comp (algebraMap ↥W₀ ↥F₀)).toAlgebra
  haveI : IsScalarTower ↥W₀ ↥F₀ ↥E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgWE : ∀ r : ↥W₀, algebraMap ↥W₀ ↥E r = algebraMap ↥F₀ ↥E (r : ↥F₀) := fun r => rfl
  haveI := hdvr
  set π : ↥W₀ := ⟨algebraMap k ↥F₀ π₀, hπ₀⟩ with hπdef
  have hπ : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hunif
  have hπ₀0 : π₀ ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply Subtype.ext
    show algebraMap k ↥F₀ π₀ = 0
    rw [h, map_zero]
  have hπF : algebraMap k F π₀ = algebraMap ↥F₀ F (algebraMap k ↥F₀ π₀) := IsScalarTower.algebraMap_apply k ↥F₀ F π₀
  have hπF0 : algebraMap k F π₀ ≠ 0 := (map_ne_zero _).mpr hπ₀0

  have hϖE : ϖ ∈ E := IntermediateField.mem_adjoin_simple_self ↥F₀ ϖ
  have hu0 : u ≠ 0 := fun h => by rw [h, zero_mul] at huv; exact zero_ne_one huv
  have huE : u ∈ E := by
    have : u = (algebraMap k F π₀)⁻¹ * ϖ ^ n := by
      rw [hϖ, ← mul_assoc, inv_mul_cancel₀ hπF0, one_mul]
    rw [this, hπF]
    exact mul_mem (inv_mem (E.algebraMap_mem _)) (pow_mem hϖE n)
  have hvE : v ∈ E := by
    rw [eq_inv_of_mul_eq_one_right huv]
    exact inv_mem huE
  set ϖE' : ↥E := ⟨ϖ, hϖE⟩ with hϖE'def
  set uE : ↥E := ⟨u, huE⟩ with huEdef
  set vE : ↥E := ⟨v, hvE⟩ with hvEdef
  have huvE : uE * vE = 1 := Subtype.ext huv

  letI algWF : Algebra ↥W₀ F := ((algebraMap ↥F₀ F).comp (algebraMap ↥W₀ ↥F₀)).toAlgebra
  haveI : IsScalarTower ↥W₀ ↥F₀ F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ↥W₀ ↥E F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hlift : ∀ (p : Polynomial k), p.Monic → (∀ i, algebraMap k ↥F₀ (p.coeff i) ∈ W₀) → ∀ (x : ↥E), Polynomial.aeval (x : F) p = 0 →
      IsIntegral ↥W₀ x := by
    intro p hp hpc x hx
    have hlifts : p.map (algebraMap k ↥F₀) ∈ Polynomial.lifts (algebraMap ↥W₀ ↥F₀) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro i
      rw [Polynomial.coeff_map]
      exact ⟨⟨_, hpc i⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts (hp.map _)
    have hxF : IsIntegral ↥W₀ (x : F) := by
      refine ⟨q, hqm, ?_⟩
      have e1 : Polynomial.eval₂ (algebraMap ↥W₀ F) (x : F) q =
          Polynomial.eval₂ (algebraMap ↥F₀ F) (x : F) (q.map (algebraMap ↥W₀ ↥F₀)) := by
        rw [Polynomial.eval₂_map]; rfl
      have e2 : Polynomial.eval₂ (algebraMap ↥F₀ F) (x : F) (p.map (algebraMap k ↥F₀)) =
          Polynomial.eval₂ (algebraMap k F) (x : F) p := by
        rw [Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq]
      rw [e1, hq, e2]
      exact hx
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥W₀ ↥E F) Subtype.val_injective).mp hxF
  have huint : IsIntegral ↥W₀ uE := hlift pu hpu hpuc uE hpu0
  have hvint : IsIntegral ↥W₀ vE := hlift pv hpv hpvc vE hpv0

  have hϖrel : ϖE' ^ n = algebraMap ↥W₀ ↥E π * uE := by
    apply Subtype.ext
    show ϖ ^ n = ((algebraMap ↥F₀ ↥E (algebraMap k ↥F₀ π₀) : ↥E) : F) * u
    rw [hϖ, hπF]
    rfl
  have hn : Module.finrank ↥F₀ ↥E ≤ n := by
    rw [IntermediateField.adjoin.finrank hϖF₀, ← hdeg]
    have hdvd := minpoly.dvd_map_of_isScalarTower k ↥F₀ ϖ
    have := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.map_monic_ne_zero (minpoly.monic hϖint))
    rwa [Polynomial.natDegree_map] at this
  obtain ⟨hfin, W, hRW, hcen, hDVR, hunifW, hres, hresK, huniq⟩ :=
    existsUnique_valuationSubring_of_pow_eq_mul ↥W₀ ↥F₀ ↥E n hn0 hn π hπ uE vE huvE huint hvint ϖE' hϖrel
  refine ⟨hfin, W, fun r => hRW r, hcen, hDVR, hunifW, hres, ?_, huniq⟩
  intro f
  exact hresK f

end Layer

section Tower

variable {k F : Type*} [Field k] [CharZero k] [Field F] [Algebra k F]
variable (F₀ : IntermediateField k F) (W₀ : ValuationSubring ↥F₀) (hdvr : IsDiscreteValuationRing ↥W₀)
  (π₀ : k) (hπ₀ : algebraMap k ↥F₀ π₀ ∈ W₀)
  (hunif : maximalIdeal ↥W₀ = Ideal.span {(⟨algebraMap k ↥F₀ π₀, hπ₀⟩ : ↥W₀)})

structure LayerData where
  ϖ : F
  n : ℕ
  u : F
  v : F
  pu : Polynomial k
  pv : Polynomial k
  hn0 : 0 < n
  hϖint : IsIntegral k ϖ
  hdeg : (minpoly k ϖ).natDegree = n
  huv : u * v = 1
  hpu : pu.Monic
  hpuc : ∀ i, algebraMap k ↥F₀ (pu.coeff i) ∈ W₀
  hpu0 : Polynomial.aeval u pu = 0
  hpv : pv.Monic
  hpvc : ∀ i, algebraMap k ↥F₀ (pv.coeff i) ∈ W₀
  hpv0 : Polynomial.aeval v pv = 0
  hϖ : ϖ ^ n = algebraMap k F π₀ * u

variable {F₀ W₀ π₀}

namespace LayerData

def E (d : LayerData F₀ W₀ π₀) : IntermediateField ↥F₀ F := IntermediateField.adjoin ↥F₀ {d.ϖ}

include hdvr hπ₀ hunif

theorem spec (d : LayerData F₀ W₀ π₀) :
    Module.finrank ↥F₀ ↥d.E = d.n ∧
    ∃ (W : ValuationSubring ↥d.E) (hRW : ∀ r : ↥W₀, algebraMap ↥F₀ ↥d.E r ∈ W),
      (∀ r ∈ maximalIdeal ↥W₀, (⟨algebraMap ↥F₀ ↥d.E r, hRW r⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      IsDiscreteValuationRing ↥W ∧
      (∃ hϖW : (⟨d.ϖ, IntermediateField.mem_adjoin_simple_self ↥F₀ d.ϖ⟩ : ↥d.E) ∈ W,
        maximalIdeal ↥W = Ideal.span {(⟨_, hϖW⟩ : ↥W)}) ∧
      (∀ w : ↥W, ∃ r : ↥W₀, w - ⟨algebraMap ↥F₀ ↥d.E r, hRW r⟩ ∈ maximalIdeal ↥W) ∧
      (∀ f : ↥F₀, algebraMap ↥F₀ ↥d.E f ∈ W ↔ ∃ r : ↥W₀, (r : ↥F₀) = f) ∧
      (∀ (W' : ValuationSubring ↥d.E) (hRW' : ∀ r : ↥W₀, algebraMap ↥F₀ ↥d.E r ∈ W'),
        (∀ r ∈ maximalIdeal ↥W₀, (⟨algebraMap ↥F₀ ↥d.E r, hRW' r⟩ : ↥W') ∈ maximalIdeal ↥W') → W' = W) :=
  layer_existsUnique_valuationSubring F₀ W₀ hdvr π₀ hπ₀ hunif d.n d.hn0 d.ϖ d.hϖint d.hdeg d.u d.v d.huv
    d.pu d.hpu d.hpuc d.hpu0 d.pv d.hpv d.hpvc d.hpv0 d.hϖ

end LayerData

end Tower

section Compat
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace IntermediateField p2m_export "IntermediateField" "toAlgebra map_le_iff_le_comap adjoin_le_iff aeval_coe mk val isIntegral_iff lift AdjoinSimple.gen inclusion ext adjoin_simple_le_iff algebraMap_apply adjoin.finiteDimensional smul_def adjoin.finrank adjoin inv_mem' toSubfield comap mem_top restrictScalars algebraMap_mem mem_bot mem_adjoin_simple_self map" end IntermediateField
p2m_open_scoped "IntermediateField" in

theorem IntermediateField.mem_valuationSubring_iff_of_le_of_unique
    (R : ValuationSubring K) (E₁ E₂ : IntermediateField K F) (hle : E₁ ≤ E₂)
    (W₁ : ValuationSubring ↥E₁) (W₂ : ValuationSubring ↥E₂)
    (hU₁ : ∀ (W' : ValuationSubring ↥E₁) (hRW' : ∀ r : ↥R, algebraMap K ↥E₁ r ∈ W'),
      (∀ r ∈ maximalIdeal ↥R, (⟨algebraMap K ↥E₁ r, hRW' r⟩ : ↥W') ∈ maximalIdeal ↥W') → W' = W₁)
    (hRW₂ : ∀ r : ↥R, algebraMap K ↥E₂ r ∈ W₂)
    (hcen₂ : ∀ r ∈ maximalIdeal ↥R, (⟨algebraMap K ↥E₂ r, hRW₂ r⟩ : ↥W₂) ∈ maximalIdeal ↥W₂)
    (f : F) (h₁ : f ∈ E₁) :
    (⟨f, h₁⟩ : ↥E₁) ∈ W₁ ↔ (⟨f, hle h₁⟩ : ↥E₂) ∈ W₂ := by
  let ι : ↥E₁ →+* ↥E₂ := (IntermediateField.inclusion hle).toRingHom
  let V : ValuationSubring ↥E₁ := W₂.comap ι
  have hV : ∀ x : ↥E₁, x ∈ V ↔ ι x ∈ W₂ := fun x => ValuationSubring.mem_comap
  have hιalg : ∀ r : K, ι (algebraMap K ↥E₁ r) = algebraMap K ↥E₂ r := fun r => rfl
  have hRV : ∀ r : ↥R, algebraMap K ↥E₁ r ∈ V := by
    intro r; rw [hV, hιalg]; exact hRW₂ r
  have hmaxV : ∀ x : ↥V, x ∈ maximalIdeal ↥V ↔ (⟨ι x, (hV _).mp x.2⟩ : ↥W₂) ∈ maximalIdeal _ := by
    intro x
    rw [← ValuationSubring.coe_mem_nonunits_iff, ← ValuationSubring.coe_mem_nonunits_iff,
      ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
    simp only [map_eq_zero_iff ι ι.injective]
    apply or_congr Iff.rfl
    rw [hV, map_inv₀]
  have hcenV : ∀ r ∈ maximalIdeal ↥R, (⟨algebraMap K ↥E₁ r, hRV r⟩ : ↥V) ∈ maximalIdeal ↥V := by
    intro r hr
    rw [hmaxV]
    exact hcen₂ r hr
  have hVeq : V = W₁ := hU₁ V hRV hcenV
  rw [← hVeq, hV]
  exact Iff.rfl

end Compat

namespace ValuationSubring p2m_export "ValuationSubring" "comap subtype coe_mem_nonunits_iff idealOfLE mem_comap neg_mem prime_idealOfLE toSubring algebraMap_apply ext mem_nonunits_iff_or zero_mem mem_nonunits_iff mk mem_or_inv_mem' mem_top mul_mem one_mem mem_or_inv_mem add_mem valuation_le_one_iff valuation inclusion valuation_eq_one_iff" end ValuationSubring
p2m_open_scoped "ValuationSubring" in

theorem ValuationSubring.exists_of_directed_layers
    {F : Type*} [Field F] {ι : Type*} [Nonempty ι]
    (E : ι → Subfield F) (V : ι → Set F)

    (hVE : ∀ i, V i ⊆ E i)
    (hV1 : ∀ i, (1 : F) ∈ V i)
    (hVadd : ∀ i, ∀ x ∈ V i, ∀ y ∈ V i, x + y ∈ V i)
    (hVneg : ∀ i, ∀ x ∈ V i, -x ∈ V i)
    (hVmul : ∀ i, ∀ x ∈ V i, ∀ y ∈ V i, x * y ∈ V i)
    (hVval : ∀ i, ∀ x ∈ E i, x ∈ V i ∨ x⁻¹ ∈ V i)

    (hdir : ∀ i j, ∃ l, E i ≤ E l ∧ E j ≤ E l)
    (hcov : ∀ x : F, ∃ i, x ∈ E i)
    (hcompat : ∀ i j, E i ≤ E j → ∀ x ∈ E i, (x ∈ V i ↔ x ∈ V j)) :
    ∃ W : ValuationSubring F,

      (∀ (x : F) (i : ι), x ∈ E i → (x ∈ W ↔ x ∈ V i)) ∧

      (∀ (x : ↥W) (i : ι), (x : F) ∈ E i → (x ∈ maximalIdeal ↥W ↔ (x : F) = 0 ∨ (x : F)⁻¹ ∉ V i)) := by
  classical

  have htrans : ∀ (i j : ι) (x : F), x ∈ E i → x ∈ E j → (x ∈ V i ↔ x ∈ V j) := by
    intro i j x hi hj
    obtain ⟨l, hil, hjl⟩ := hdir i j
    rw [hcompat i l hil x hi, hcompat j l hjl x hj]
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hV0 : ∀ i, (0 : F) ∈ V i := by
    intro i
    have h := hVadd i 1 (hV1 i) (-1) (hVneg i 1 (hV1 i))
    rwa [add_neg_cancel] at h
  let W : ValuationSubring F :=
    { carrier := {x | ∃ i, x ∈ E i ∧ x ∈ V i}
      mul_mem' := by
        rintro x y ⟨i, hxi, hxV⟩ ⟨j, hyj, hyV⟩
        obtain ⟨l, hil, hjl⟩ := hdir i j
        exact ⟨l, (E l).mul_mem (hil hxi) (hjl hyj),
          hVmul l x ((hcompat i l hil x hxi).1 hxV) y ((hcompat j l hjl y hyj).1 hyV)⟩
      one_mem' := ⟨i₀, (E i₀).one_mem, hV1 i₀⟩
      add_mem' := by
        rintro x y ⟨i, hxi, hxV⟩ ⟨j, hyj, hyV⟩
        obtain ⟨l, hil, hjl⟩ := hdir i j
        exact ⟨l, (E l).add_mem (hil hxi) (hjl hyj),
          hVadd l x ((hcompat i l hil x hxi).1 hxV) y ((hcompat j l hjl y hyj).1 hyV)⟩
      zero_mem' := ⟨i₀, (E i₀).zero_mem, hV0 i₀⟩
      neg_mem' := by
        rintro x ⟨i, hxi, hxV⟩
        exact ⟨i, (E i).neg_mem hxi, hVneg i x hxV⟩
      mem_or_inv_mem' := by
        intro x
        obtain ⟨i, hxi⟩ := hcov x
        rcases hVval i x hxi with h | h
        · exact Or.inl ⟨i, hxi, h⟩
        · exact Or.inr ⟨i, (E i).inv_mem hxi, h⟩ }
  have hmemW : ∀ x : F, x ∈ W ↔ ∃ i, x ∈ E i ∧ x ∈ V i := fun _ => Iff.rfl
  have h1 : ∀ (x : F) (i : ι), x ∈ E i → (x ∈ W ↔ x ∈ V i) := by
    intro x i hxi
    rw [hmemW]
    constructor
    · rintro ⟨j, hxj, hxV⟩
      exact (htrans j i x hxj hxi).1 hxV
    · intro h
      exact ⟨i, hxi, h⟩
  refine ⟨W, h1, ?_⟩
  intro x i hxi
  have hunit : IsUnit x ↔ ((x : F) ≠ 0 ∧ (x : F)⁻¹ ∈ W) := by
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hx.exists_right_inv
      have hF : (x : F) * (y : F) = 1 := by
        have := congrArg (fun z : ↥W => (z : F)) hy
        simpa using this
      refine ⟨left_ne_zero_of_mul_eq_one hF, ?_⟩
      rw [inv_eq_of_mul_eq_one_right hF]
      exact y.2
    · rintro ⟨hne, hinv⟩
      have hxy : x * ⟨(x : F)⁻¹, hinv⟩ = 1 := by
        apply Subtype.ext
        show (x : F) * (x : F)⁻¹ = 1
        exact mul_inv_cancel₀ hne
      have hyx : (⟨(x : F)⁻¹, hinv⟩ : ↥W) * x = 1 := by
        rw [mul_comm]; exact hxy
      exact ⟨⟨x, ⟨(x : F)⁻¹, hinv⟩, hxy, hyx⟩, rfl⟩
  rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff, hunit, not_and_or, not_not,
    h1 _ i ((E i).inv_mem hxi)]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 25600000 in

theorem solution
    (k F : Type) [Field k] [CharZero k] [Field F] [Algebra k F]
    (L F₀ : IntermediateField k F) (hgen : L ⊔ F₀ = ⊤)
    (A : ValuationSubring ↥L) (W₀ : ValuationSubring ↥F₀)
    (hagree : ∀ x : k, algebraMap k ↥L x ∈ A ↔ algebraMap k ↥F₀ x ∈ W₀)
    (hdvr : IsDiscreteValuationRing ↥W₀)
    (π₀ : k) (hπ₀ : algebraMap k ↥F₀ π₀ ∈ W₀)
    (hunif : maximalIdeal ↥W₀ = Ideal.span {(⟨algebraMap k ↥F₀ π₀, hπ₀⟩ : ↥W₀)})

    (hint : ∀ a : ↥L, a ∈ A → IsIntegral ↥(A.comap (algebraMap k ↥L)) a)

    (htower : ∀ s : Finset ↥L, ∃ (n : ℕ) (ϖ' : ↥L) (u v : ↥A), 0 < n ∧ ϖ' ∈ A ∧ (u : ↥L) * v = 1 ∧
        (∀ x ∈ s, (x : F) ∈ IntermediateField.adjoin k {((ϖ' : ↥L) : F)}) ∧
        Module.finrank k ↥(IntermediateField.adjoin k {((ϖ' : ↥L) : F)}) = n ∧
        ϖ' ^ n = algebraMap k ↥L π₀ * (u : ↥L) ∧
        (∀ a : ↥L, a ∈ A → (a : F) ∈ IntermediateField.adjoin k {((ϖ' : ↥L) : F)} → a ≠ 0 →
          ∃ (m : ℕ) (w z : ↥A), (w : ↥L) * z = 1 ∧ a = ϖ' ^ m * (w : ↥L))) :
    ∃ W : ValuationSubring F,
      (∀ x : ↥L, (x : F) ∈ W ↔ x ∈ A) ∧
      (∀ f : ↥F₀, (f : F) ∈ W ↔ f ∈ W₀) ∧
      (∀ w : ↥W, ∃ (f : ↥W₀) (h : ((f : ↥F₀) : F) ∈ W), w - ⟨_, h⟩ ∈ maximalIdeal ↥W) ∧
      (∀ f : F, f ≠ 0 → ∃ c : ↥L, (c : F) ≠ 0 ∧ ∃ h : (c : F) * f ∈ W, IsUnit (⟨_, h⟩ : ↥W)) := by
  classical
  haveI := hdvr
  set A₀ := A.comap (algebraMap k ↥L) with hA₀def
  have hA₀mem : ∀ a : k, a ∈ A₀ ↔ algebraMap k ↥L a ∈ A := fun a => ValuationSubring.mem_comap
  have hπW₀0 : (⟨algebraMap k ↥F₀ π₀, hπ₀⟩ : ↥W₀) ≠ 0 :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hunif).ne_zero
  have hπ₀0 : π₀ ≠ 0 := by
    intro h; apply hπW₀0; apply Subtype.ext; show algebraMap k ↥F₀ π₀ = 0; rw [h, map_zero]

  have hpoly : ∀ a : ↥L, a ∈ A → ∃ p : Polynomial k, p.Monic ∧ (∀ i, algebraMap k ↥F₀ (p.coeff i) ∈ W₀) ∧
      Polynomial.aeval (a : F) p = 0 := by
    intro a ha
    obtain ⟨p, hp, hp0⟩ := hint a ha
    refine ⟨p.map A₀.subtype, hp.map _, fun i => ?_, ?_⟩
    · rw [Polynomial.coeff_map, ← hagree, ← hA₀mem]
      exact (p.coeff i).2
    · have h1 : Polynomial.aeval a (p.map A₀.subtype) = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map]
        exact hp0
      rw [IntermediateField.aeval_coe L a, h1]
      rfl

  have hlayer : ∀ s : Finset ↥L, ∃ (d : LayerData F₀ W₀ π₀) (ϖL : ↥L), (ϖL : F) = d.ϖ ∧ ϖL ∈ A ∧
      (∀ x ∈ s, (x : F) ∈ IntermediateField.adjoin k {d.ϖ}) ∧
      (∀ a : ↥L, a ∈ A → (a : F) ∈ IntermediateField.adjoin k {d.ϖ} → a ≠ 0 →
        ∃ (m : ℕ) (w z : ↥A), (w : ↥L) * z = 1 ∧ a = ϖL ^ m * (w : ↥L)) ∧
      (∀ y : F, y ∈ IntermediateField.adjoin k {d.ϖ} → y ∈ d.E) := by
    intro s
    obtain ⟨n, ϖ', u, v, hn0, hϖA, huv, hs, hfin, hϖn, hunifA⟩ := htower s
    obtain ⟨pu, hpu, hpuc, hpu0⟩ := hpoly u u.2
    obtain ⟨pv, hpv, hpvc, hpv0⟩ := hpoly v v.2

    haveI : FiniteDimensional k ↥(IntermediateField.adjoin k {((ϖ' : ↥L) : F)}) :=
      Module.finite_of_finrank_pos (by omega)
    have hϖint : IsIntegral k ((ϖ' : ↥L) : F) := by
      have h1 : IsIntegral k (IntermediateField.AdjoinSimple.gen k ((ϖ' : ↥L) : F)) := IsIntegral.of_finite k _
      have h2 := h1.map (IntermediateField.val _)
      simpa using h2
    have hdeg : (minpoly k ((ϖ' : ↥L) : F)).natDegree = n := by
      rw [← IntermediateField.adjoin.finrank hϖint]; exact hfin
    have huvF : ((u : ↥L) : F) * ((v : ↥L) : F) = 1 := by
      have := congrArg (fun z : ↥L => (z : F)) huv; simpa using this
    have hϖF : ((ϖ' : ↥L) : F) ^ n = algebraMap k F π₀ * ((u : ↥L) : F) := by
      have := congrArg (fun z : ↥L => (z : F)) hϖn
      simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul] at this
      rw [this]
      rfl
    let d : LayerData F₀ W₀ π₀ :=
      { ϖ := ((ϖ' : ↥L) : F), n := n, u := ((u : ↥L) : F), v := ((v : ↥L) : F), pu := pu, pv := pv,
        hn0 := hn0, hϖint := hϖint, hdeg := hdeg, huv := huvF, hpu := hpu, hpuc := hpuc, hpu0 := hpu0,
        hpv := hpv, hpvc := hpvc, hpv0 := hpv0, hϖ := hϖF }
    have hkE : ∀ y : F, y ∈ IntermediateField.adjoin k {d.ϖ} → y ∈ d.E := by
      intro y hy
      have hle : IntermediateField.adjoin k {d.ϖ} ≤ (d.E).restrictScalars k := by
        rw [IntermediateField.adjoin_le_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact IntermediateField.mem_adjoin_simple_self ↥F₀ d.ϖ
      exact hle hy
    exact ⟨d, ϖ', rfl, hϖA, hs, fun a ha haE ha0 => hunifA a ha haE ha0, hkE⟩

  choose D ϖL hϖLD hϖLA hDs hDunif hDkE using hlayer
  choose Wd hWd using fun d : LayerData F₀ W₀ π₀ => (d.spec hdvr hπ₀ hunif).2
  have hRW : ∀ d (r : ↥W₀), algebraMap ↥F₀ ↥d.E r ∈ Wd d := fun d => (hWd d).choose
  have hcen : ∀ d, ∀ r ∈ maximalIdeal ↥W₀, (⟨algebraMap ↥F₀ ↥d.E r, hRW d r⟩ : ↥(Wd d)) ∈ maximalIdeal _ :=
    fun d => (hWd d).choose_spec.1
  have hdvrW : ∀ d, IsDiscreteValuationRing ↥(Wd d) := fun d => (hWd d).choose_spec.2.1
  have hunifW : ∀ d, ∃ hϖW : (⟨d.ϖ, IntermediateField.mem_adjoin_simple_self ↥F₀ d.ϖ⟩ : ↥d.E) ∈ Wd d,
      maximalIdeal ↥(Wd d) = Ideal.span {(⟨_, hϖW⟩ : ↥(Wd d))} := fun d => (hWd d).choose_spec.2.2.1
  have hresW : ∀ d (w : ↥(Wd d)), ∃ r : ↥W₀, w - ⟨algebraMap ↥F₀ ↥d.E r, hRW d r⟩ ∈ maximalIdeal _ :=
    fun d => (hWd d).choose_spec.2.2.2.1
  have hresK : ∀ (d : LayerData F₀ W₀ π₀) (f : ↥F₀), algebraMap ↥F₀ ↥d.E f ∈ Wd d ↔ ∃ r : ↥W₀, (r : ↥F₀) = f :=
    fun d => (hWd d).choose_spec.2.2.2.2.1
  have huniq : ∀ (d : LayerData F₀ W₀ π₀) (W' : ValuationSubring ↥d.E) (hRW' : ∀ r : ↥W₀, algebraMap ↥F₀ ↥d.E r ∈ W'),
      (∀ r ∈ maximalIdeal ↥W₀, (⟨algebraMap ↥F₀ ↥d.E r, hRW' r⟩ : ↥W') ∈ maximalIdeal ↥W') → W' = Wd d :=
    fun d => (hWd d).choose_spec.2.2.2.2.2

  have hcompat : ∀ (d₁ d₂ : LayerData F₀ W₀ π₀) (hle : d₁.E ≤ d₂.E) (f : F) (h₁ : f ∈ d₁.E),
      (⟨f, h₁⟩ : ↥d₁.E) ∈ Wd d₁ ↔ (⟨f, hle h₁⟩ : ↥d₂.E) ∈ Wd d₂ :=
    fun d₁ d₂ hle f h₁ => IntermediateField.mem_valuationSubring_iff_of_le_of_unique W₀ d₁.E d₂.E hle (Wd d₁) (Wd d₂)
      (huniq d₁) (hRW d₂) (hcen d₂) f h₁
  let Es : Finset ↥L → Subfield F := fun s => ((D s).E).toSubfield
  have hEs : ∀ s (x : F), x ∈ Es s ↔ x ∈ (D s).E := fun s x => Iff.rfl
  let V : Finset ↥L → Set F := fun s => {x | ∃ h : x ∈ (D s).E, (⟨x, h⟩ : ↥(D s).E) ∈ Wd (D s)}
  have hV : ∀ s (x : F) (h : x ∈ (D s).E), x ∈ V s ↔ (⟨x, h⟩ : ↥(D s).E) ∈ Wd (D s) :=
    fun s x h => ⟨fun ⟨_, hh⟩ => hh, fun hh => ⟨h, hh⟩⟩
  have hVE : ∀ s, V s ⊆ Es s := fun s x ⟨h, _⟩ => h

  have hmono : ∀ s t : Finset ↥L, ϖL s ∈ t → (D s).E ≤ (D t).E := by
    intro s t hst
    show IntermediateField.adjoin ↥F₀ {(D s).ϖ} ≤ (D t).E
    rw [IntermediateField.adjoin_simple_le_iff, ← hϖLD s]
    exact hDkE t _ (hDs t _ hst)
  have hdir : ∀ s t : Finset ↥L, ∃ l, Es s ≤ Es l ∧ Es t ≤ Es l := by
    intro s t
    refine ⟨insert (ϖL s) (insert (ϖL t) ∅), ?_, ?_⟩
    · exact fun x hx => hmono s _ (Finset.mem_insert_self _ _) hx
    · exact fun x hx => hmono t _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hx
  have hcompatV : ∀ s t, Es s ≤ Es t → ∀ x ∈ Es s, (x ∈ V s ↔ x ∈ V t) := by
    intro s t hle x hx
    rw [hV s x hx, hV t x (hle hx)]
    exact hcompat (D s) (D t) hle x hx

  have hF₀E : ∀ s (f : ↥F₀), (f : F) ∈ Es s := fun s f => ((D s).E).algebraMap_mem f
  have hLE : ∀ x : ↥L, (x : F) ∈ Es (insert x ∅) :=
    fun x => hDkE _ _ (hDs _ x (Finset.mem_insert_self _ _))
  have hcov : ∀ x : F, ∃ s, x ∈ Es s := by
    let U : IntermediateField k F :=
      { carrier := {y | ∃ s, y ∈ Es s}
        mul_mem' := by
          rintro a b ⟨s, ha⟩ ⟨t, hb⟩
          obtain ⟨l, hsl, htl⟩ := hdir s t
          exact ⟨l, (Es l).mul_mem (hsl ha) (htl hb)⟩
        one_mem' := ⟨∅, (Es ∅).one_mem⟩
        add_mem' := by
          rintro a b ⟨s, ha⟩ ⟨t, hb⟩
          obtain ⟨l, hsl, htl⟩ := hdir s t
          exact ⟨l, (Es l).add_mem (hsl ha) (htl hb)⟩
        zero_mem' := ⟨∅, (Es ∅).zero_mem⟩
        algebraMap_mem' := fun r => ⟨∅, by rw [IsScalarTower.algebraMap_apply k ↥F₀ F]; exact hF₀E ∅ _⟩
        inv_mem' := by
          rintro a ⟨s, ha⟩
          exact ⟨s, (Es s).inv_mem ha⟩ }
    have hU : ∀ y : F, y ∈ U ↔ ∃ s, y ∈ Es s := fun y => Iff.rfl
    have htop : (⊤ : IntermediateField k F) ≤ U := by
      rw [← hgen]
      refine sup_le ?_ ?_
      · intro y hy; exact (hU y).mpr ⟨_, hLE ⟨y, hy⟩⟩
      · intro y hy; exact (hU y).mpr ⟨∅, hF₀E ∅ ⟨y, hy⟩⟩
    intro x
    exact (hU x).mp (htop (IntermediateField.mem_top))

  have hV1 : ∀ s, (1 : F) ∈ V s := fun s => ⟨(D s).E.one_mem, (Wd (D s)).one_mem⟩
  have hVadd : ∀ s, ∀ x ∈ V s, ∀ y ∈ V s, x + y ∈ V s :=
    fun s x ⟨hx, hx'⟩ y ⟨hy, hy'⟩ => ⟨(D s).E.add_mem hx hy, (Wd (D s)).add_mem _ _ hx' hy'⟩
  have hVneg : ∀ s, ∀ x ∈ V s, -x ∈ V s := fun s x ⟨hx, hx'⟩ => ⟨(D s).E.neg_mem hx, (Wd (D s)).neg_mem _ hx'⟩
  have hVmul : ∀ s, ∀ x ∈ V s, ∀ y ∈ V s, x * y ∈ V s :=
    fun s x ⟨hx, hx'⟩ y ⟨hy, hy'⟩ => ⟨(D s).E.mul_mem hx hy, (Wd (D s)).mul_mem _ _ hx' hy'⟩
  have hVval : ∀ s, ∀ x ∈ Es s, x ∈ V s ∨ x⁻¹ ∈ V s := by
    intro s x hx
    rcases (Wd (D s)).mem_or_inv_mem ⟨x, hx⟩ with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨(D s).E.inv_mem hx, h⟩
  haveI : Nonempty (Finset ↥L) := ⟨∅⟩
  obtain ⟨W, hWmem, hWmax⟩ := ValuationSubring.exists_of_directed_layers Es V hVE hV1 hVadd hVneg hVmul hVval hdir hcov hcompatV

  have hmaxWd : ∀ (d : LayerData F₀ W₀ π₀) (y : ↥(Wd d)), y ∈ maximalIdeal ↥(Wd d) ↔ (y : ↥d.E) = 0 ∨ (y : ↥d.E)⁻¹ ∉ Wd d := by
    intro d y
    rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]

  have hAW : ∀ s (x : ↥L) (hx : (x : F) ∈ (D s).E), x ∈ A → (⟨(x : F), hx⟩ : ↥(D s).E) ∈ Wd (D s) := by
    intro s x hx hxA
    obtain ⟨p, hp, hpc, hp0⟩ := hpoly x hxA

    set E := (D s).E
    set y : ↥E := ⟨(x : F), hx⟩ with hydef
    letI algWE : Algebra ↥W₀ ↥E := ((algebraMap ↥F₀ ↥E).comp (algebraMap ↥W₀ ↥F₀)).toAlgebra
    haveI : IsScalarTower ↥W₀ ↥F₀ ↥E := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI algWF : Algebra ↥W₀ F := ((algebraMap ↥F₀ F).comp (algebraMap ↥W₀ ↥F₀)).toAlgebra
    haveI : IsScalarTower ↥W₀ ↥F₀ F := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower ↥W₀ ↥E F := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hlifts : p.map (algebraMap k ↥F₀) ∈ Polynomial.lifts (algebraMap ↥W₀ ↥F₀) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro i; rw [Polynomial.coeff_map]; exact ⟨⟨_, hpc i⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts (hp.map _)
    have hyF : IsIntegral ↥W₀ (x : F) := by
      refine ⟨q, hqm, ?_⟩
      have e1 : Polynomial.eval₂ (algebraMap ↥W₀ F) (x : F) q =
          Polynomial.eval₂ (algebraMap ↥F₀ F) (x : F) (q.map (algebraMap ↥W₀ ↥F₀)) := by
        rw [Polynomial.eval₂_map]; rfl
      have e2 : Polynomial.eval₂ (algebraMap ↥F₀ F) (x : F) (p.map (algebraMap k ↥F₀)) =
          Polynomial.eval₂ (algebraMap k F) (x : F) p := by
        rw [Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq]
      rw [e1, hq, e2]; exact hp0
    have hyE : IsIntegral ↥W₀ y := (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥W₀ ↥E F) Subtype.val_injective).mp hyF

    letI algWdW : Algebra ↥W₀ ↥(Wd (D s)) := ((algebraMap ↥W₀ ↥E).codRestrict (Wd (D s)).toSubring (fun r => hRW (D s) r)).toAlgebra
    haveI : IsScalarTower ↥W₀ ↥(Wd (D s)) ↥E := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hyWd : IsIntegral ↥(Wd (D s)) y := hyE.tower_top
    obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥(Wd (D s))) (K := ↥E)).mp hyWd
    rw [← hz]; exact z.2
  refine ⟨W, fun x => ?_, fun f => ?_, fun w => ?_, fun f hf0 => ?_⟩
  ·
    set s : Finset ↥L := insert x ∅ with hsdef
    have hxk : (x : F) ∈ IntermediateField.adjoin k {(D s).ϖ} := hDs s x (Finset.mem_insert_self _ _)
    have hxE : (x : F) ∈ (D s).E := hDkE s _ hxk
    rw [hWmem (x : F) s hxE, hV s (x : F) hxE]
    refine ⟨fun hxW => ?_, fun hxA => hAW s x hxE hxA⟩
    by_contra hxA
    have hx0 : x ≠ 0 := fun h => hxA (h ▸ A.zero_mem)
    have hxinvA : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hxA
    have hxinvk : ((x⁻¹ : ↥L) : F) ∈ IntermediateField.adjoin k {(D s).ϖ} := by
      have : ((x⁻¹ : ↥L) : F) = ((x : ↥L) : F)⁻¹ := by simp
      rw [this]; exact (IntermediateField.adjoin k {(D s).ϖ}).inv_mem hxk
    obtain ⟨m, w, z, hwz, hxm⟩ := hDunif s x⁻¹ hxinvA hxinvk (inv_ne_zero hx0)

    have hm : m ≠ 0 := by
      intro hm0
      rw [hm0, pow_zero, one_mul] at hxm
      apply hxA
      have : x = (z : ↥L) := by
        have h1 : x⁻¹ * (z : ↥L) = 1 := by rw [hxm]; exact hwz
        calc x = x * (x⁻¹ * (z : ↥L)) := by rw [h1, mul_one]
          _ = (z : ↥L) := by rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
      rw [this]; exact z.2

    obtain ⟨hϖW, hgen⟩ := hunifW (D s)
    haveI := hdvrW (D s)
    have hϖ0F : (D s).ϖ ≠ 0 := fun h =>
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hgen).ne_zero (Subtype.ext (Subtype.ext h))
    have hxinvE : ((x : ↥L) : F)⁻¹ ∈ (D s).E := (D s).E.inv_mem hxE
    have hxmF : ((x : ↥L) : F)⁻¹ = (D s).ϖ ^ m * ((w : ↥L) : F) := by
      have := congrArg (fun t : ↥L => (t : F)) hxm
      push_cast at this
      rw [this, hϖLD]
    have hwE : ((w : ↥L) : F) ∈ (D s).E := by
      have : ((w : ↥L) : F) = ((D s).ϖ ^ m)⁻¹ * ((x : ↥L) : F)⁻¹ := by
        rw [hxmF, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hϖ0F), one_mul]
      rw [this]
      exact (D s).E.mul_mem ((D s).E.inv_mem (pow_mem (IntermediateField.mem_adjoin_simple_self ↥F₀ (D s).ϖ) m)) hxinvE
    have hwW : (⟨((w : ↥L) : F), hwE⟩ : ↥(D s).E) ∈ Wd (D s) := hAW s (w : ↥L) hwE w.2
    have hxinvW : (⟨((x : ↥L) : F)⁻¹, hxinvE⟩ : ↥(D s).E) ∈ Wd (D s) := by
      have : (⟨((x : ↥L) : F)⁻¹, hxinvE⟩ : ↥(D s).E) =
          (⟨(D s).ϖ, IntermediateField.mem_adjoin_simple_self ↥F₀ (D s).ϖ⟩ : ↥(D s).E) ^ m * ⟨((w : ↥L) : F), hwE⟩ := by
        apply Subtype.ext
        exact hxmF
      rw [this]
      exact (Wd (D s)).mul_mem _ _ (pow_mem hϖW m) hwW
    have hxinvmax : (⟨_, hxinvW⟩ : ↥(Wd (D s))) ∈ maximalIdeal ↥(Wd (D s)) := by
      have : (⟨_, hxinvW⟩ : ↥(Wd (D s))) = (⟨_, hϖW⟩ : ↥(Wd (D s))) ^ m * ⟨_, hwW⟩ := by
        apply Subtype.ext; apply Subtype.ext
        exact hxmF
      rw [this, hgen]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) m |> fun h =>
        Ideal.pow_le_self hm h)

    have hunit : IsUnit (⟨_, hxinvW⟩ : ↥(Wd (D s))) :=
      isUnit_iff_exists_inv.mpr ⟨⟨_, hxW⟩, Subtype.ext (Subtype.ext (inv_mul_cancel₀ (by
        exact_mod_cast Subtype.coe_ne_coe.mpr hx0)))⟩
    exact (IsLocalRing.mem_maximalIdeal _).mp hxinvmax hunit
  ·
    have hfE : (f : F) ∈ (D ∅).E := hF₀E ∅ f
    rw [hWmem (f : F) ∅ hfE, hV ∅ (f : F) hfE]
    have : (⟨(f : F), hfE⟩ : ↥(D ∅).E) = algebraMap ↥F₀ ↥(D ∅).E f := rfl
    rw [this, hresK]
    exact ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun hf => ⟨⟨f, hf⟩, rfl⟩⟩
  ·
    obtain ⟨s, hwE⟩ := hcov (w : F)
    have hwW : (⟨(w : F), hwE⟩ : ↥(D s).E) ∈ Wd (D s) := (hV s _ hwE).mp ((hWmem _ s hwE).mp w.2)
    obtain ⟨r, hr⟩ := hresW (D s) ⟨_, hwW⟩
    have hrW : ((r : ↥F₀) : F) ∈ W := (hWmem _ ∅ (hF₀E ∅ r)).mpr ((hV ∅ _ (hF₀E ∅ r)).mpr (by
      have : (⟨((r : ↥F₀) : F), hF₀E ∅ r⟩ : ↥(D ∅).E) = algebraMap ↥F₀ ↥(D ∅).E r := rfl
      rw [this]; exact hRW (D ∅) r))
    refine ⟨r, hrW, ?_⟩
    have hzE : ((w - ⟨_, hrW⟩ : ↥W) : F) ∈ Es s := (Es s).sub_mem hwE (hF₀E s r)
    rw [hWmax _ s hzE]
    rw [hmaxWd] at hr
    rcases hr with h | h
    · left
      have := congrArg (fun t : ↥(D s).E => (t : F)) h
      simpa using this
    · right
      intro hinv
      apply h
      have hzE' : ((w : F) - ((r : ↥F₀) : F))⁻¹ ∈ (D s).E := (D s).E.inv_mem ((D s).E.sub_mem hwE (hF₀E s r))
      have := (hV s _ hzE').mp hinv
      convert this using 1
      exact Subtype.ext rfl
  ·
    obtain ⟨s, hfE⟩ := hcov f
    haveI := hdvrW (D s)
    obtain ⟨hϖW, hgen⟩ := hunifW (D s)
    set ϖW : ↥(Wd (D s)) := ⟨_, hϖW⟩ with hϖWdef
    have hϖirr : Irreducible ϖW := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hgen
    set fE : ↥(D s).E := ⟨f, hfE⟩ with hfEdef
    have hfE0 : fE ≠ 0 := fun h => hf0 (congrArg Subtype.val h)

    have hunitW : ∀ (y : F) (hyE : y ∈ (D s).E) (hyWd : (⟨y, hyE⟩ : ↥(D s).E) ∈ Wd (D s)),
        IsUnit (⟨⟨y, hyE⟩, hyWd⟩ : ↥(Wd (D s))) → ∃ h : y ∈ W, IsUnit (⟨y, h⟩ : ↥W) := by
      intro y hyE hyWd hu
      have hyW : y ∈ W := (hWmem y s hyE).mpr ((hV s y hyE).mpr hyWd)
      refine ⟨hyW, ?_⟩
      by_contra hnu
      have hmax : (⟨y, hyW⟩ : ↥W) ∈ maximalIdeal ↥W := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rw [hWmax _ s hyE] at hmax
      have hmax' : (⟨⟨y, hyE⟩, hyWd⟩ : ↥(Wd (D s))) ∈ maximalIdeal _ := by
        rw [hmaxWd]
        rcases hmax with h | h
        · left; exact Subtype.ext h
        · right; intro h2; exact h ((hV s _ ((D s).E.inv_mem hyE)).mpr h2)
      exact (IsLocalRing.mem_maximalIdeal _).mp hmax' hu
    rcases (Wd (D s)).mem_or_inv_mem fE with hfW | hfW
    ·
      have hfW0 : (⟨fE, hfW⟩ : ↥(Wd (D s))) ≠ 0 := fun h => hfE0 (congrArg Subtype.val h)
      obtain ⟨m, uu, hfu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfW0 hϖirr
      have hϖL0 : ϖL s ≠ 0 := fun h => by
        apply hϖirr.ne_zero; apply Subtype.ext; apply Subtype.ext
        show (D s).ϖ = 0
        rw [← hϖLD, h]
        rfl
      refine ⟨(ϖL s)⁻¹ ^ m, fun h => (pow_ne_zero m (inv_ne_zero hϖL0)) (ZeroMemClass.coe_eq_zero.mp h), ?_⟩

      have hϖval : (((ϖW : ↥(Wd (D s))) : ↥(D s).E) : F) = ((ϖL s : ↥L) : F) := by rw [hϖLD]
      have hP0 : ((ϖL s : ↥L) : F) ^ m ≠ 0 := pow_ne_zero _ (fun h => hϖL0 (ZeroMemClass.coe_eq_zero.mp h))
      have hfUP : f = (((uu : ↥(Wd (D s))) : ↥(D s).E) : F) * ((ϖL s : ↥L) : F) ^ m := by
        have h1 := congrArg (fun t : ↥(Wd (D s)) => ((t : ↥(D s).E) : F)) hfu
        push_cast at h1
        rw [hϖval] at h1
        exact h1
      have hcf : (((ϖL s)⁻¹ ^ m : ↥L) : F) * f = (((uu : ↥(Wd (D s))) : ↥(D s).E) : F) := by
        push_cast
        rw [hfUP, inv_pow, mul_comm (((uu : ↥(Wd (D s))) : ↥(D s).E) : F), ← mul_assoc, inv_mul_cancel₀ hP0, one_mul]
      have huE : (((uu : ↥(Wd (D s))) : ↥(D s).E) : F) ∈ (D s).E := ((uu : ↥(Wd (D s))) : ↥(D s).E).2
      have huWd : (⟨_, huE⟩ : ↥(D s).E) ∈ Wd (D s) := by
        have : (⟨_, huE⟩ : ↥(D s).E) = ((uu : ↥(Wd (D s))) : ↥(D s).E) := rfl
        rw [this]; exact ((uu : ↥(Wd (D s)))).2
      obtain ⟨h, hu⟩ := hunitW _ huE huWd (by
        have : (⟨⟨_, huE⟩, huWd⟩ : ↥(Wd (D s))) = (uu : ↥(Wd (D s))) := rfl
        rw [this]; exact Units.isUnit uu)
      rw [hcf]
      exact ⟨h, hu⟩
    ·
      have hfinv0 : (⟨fE⁻¹, hfW⟩ : ↥(Wd (D s))) ≠ 0 := fun h => inv_ne_zero hfE0 (congrArg Subtype.val h)
      obtain ⟨m, uu, hfu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfinv0 hϖirr
      have hϖL0 : ϖL s ≠ 0 := fun h => by
        apply hϖirr.ne_zero; apply Subtype.ext; apply Subtype.ext
        show (D s).ϖ = 0
        rw [← hϖLD, h]
        rfl
      refine ⟨(ϖL s) ^ m, fun h => (pow_ne_zero m hϖL0) (ZeroMemClass.coe_eq_zero.mp h), ?_⟩

      have hϖval : (((ϖW : ↥(Wd (D s))) : ↥(D s).E) : F) = ((ϖL s : ↥L) : F) := by rw [hϖLD]
      have hP0 : ((ϖL s : ↥L) : F) ^ m ≠ 0 := pow_ne_zero _ (fun h => hϖL0 (ZeroMemClass.coe_eq_zero.mp h))
      have hfinv : f⁻¹ = ((((uu : (↥(Wd (D s)))ˣ) : ↥(Wd (D s))) : ↥(D s).E) : F) * ((ϖL s : ↥L) : F) ^ m := by
        have h1 := congrArg (fun t : ↥(Wd (D s)) => ((t : ↥(D s).E) : F)) hfu
        push_cast at h1
        rw [hϖval] at h1
        exact h1
      have huinv : ((((uu⁻¹ : (↥(Wd (D s)))ˣ) : ↥(Wd (D s))) : ↥(D s).E) : F) *
          ((((uu : (↥(Wd (D s)))ˣ) : ↥(Wd (D s))) : ↥(D s).E) : F) = 1 := by
        have h0 : ((uu⁻¹ : (↥(Wd (D s)))ˣ) : ↥(Wd (D s))) * (uu : ↥(Wd (D s))) = 1 := Units.inv_mul uu
        have := congrArg (fun t : ↥(Wd (D s)) => ((t : ↥(D s).E) : F)) h0
        push_cast at this
        exact this
      have hcf : (((ϖL s) ^ m : ↥L) : F) * f = ((((uu⁻¹ : (↥(Wd (D s)))ˣ) : ↥(Wd (D s))) : ↥(D s).E) : F) := by
        push_cast
        calc ((ϖL s : ↥L) : F) ^ m * f = ((ϖL s : ↥L) : F) ^ m * (f⁻¹)⁻¹ := by rw [inv_inv]
          _ = ((ϖL s : ↥L) : F) ^ m * (((((uu : (↥(Wd (D s)))ˣ) : ↥(Wd (D s))) : ↥(D s).E) : F) * ((ϖL s : ↥L) : F) ^ m)⁻¹ := by
              rw [hfinv]
          _ = ((((uu : (↥(Wd (D s)))ˣ) : ↥(Wd (D s))) : ↥(D s).E) : F)⁻¹ := by
              rw [mul_inv, mul_comm ((((uu : (↥(Wd (D s)))ˣ) : ↥(Wd (D s))) : ↥(D s).E) : F)⁻¹, ← mul_assoc,
                mul_inv_cancel₀ hP0, one_mul]
          _ = ((((uu⁻¹ : (↥(Wd (D s)))ˣ) : ↥(Wd (D s))) : ↥(D s).E) : F) := (eq_inv_of_mul_eq_one_left huinv).symm
      have huE : ((((uu⁻¹ : (↥(Wd (D s)))ˣ) : ↥(Wd (D s))) : ↥(D s).E) : F) ∈ (D s).E := ((((uu⁻¹ : (↥(Wd (D s)))ˣ) : ↥(Wd (D s))) : ↥(D s).E)).2
      have huWd : (⟨_, huE⟩ : ↥(D s).E) ∈ Wd (D s) := by
        have : (⟨_, huE⟩ : ↥(D s).E) = (((uu⁻¹ : (↥(Wd (D s)))ˣ) : ↥(Wd (D s))) : ↥(D s).E) := rfl
        rw [this]; exact (((uu⁻¹ : (↥(Wd (D s)))ˣ) : ↥(Wd (D s)))).2
      obtain ⟨h, hu⟩ := hunitW _ huE huWd (by
        have : (⟨⟨_, huE⟩, huWd⟩ : ↥(Wd (D s))) = ((uu⁻¹ : (↥(Wd (D s)))ˣ) : ↥(Wd (D s))) := rfl
        rw [this]; exact Units.isUnit _)
      rw [hcf]
      exact ⟨h, hu⟩

end S_ValuationSubring_exists_constantsTower_of_totallyRamified_of_isIntegral
end P2MW
export P2MW.S_ValuationSubring_exists_constantsTower_of_totallyRamified_of_isIntegral (solution)
