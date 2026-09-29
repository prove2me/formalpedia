-- Prove2me | solution 1 for ValuationSubring.exists_isDiscreteValuationRing_dominates_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/79046e99-6aaa-550c-8a65-2cf08d4498e2

import Mathlib
import Theorems.Thm_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional

set_option autoImplicit false

universe u v

open IsLocalRing

namespace DvrExtFinite

theorem dimensionLEOne_of_ringKrullDim_le_one (C : Type v) [CommRing C] [IsDomain C]
    (h : ringKrullDim C ≤ 1) : Ring.DimensionLEOne C := by
  refine Ring.DimensionLEOne.mk (fun {p} hp0 hp => ?_)
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  by_contra hnot
  have hlt : p < m := lt_of_le_of_ne hpm (fun h => hnot (h ▸ hm))
  have hbot : (⊥ : Ideal C) < p := bot_lt_iff_ne_bot.mpr hp0
  haveI := hm.isPrime
  have h1 : (⊥ : Ideal C).height + 1 ≤ p.height := Ideal.height_add_one_le_of_lt_of_isPrime hbot
  have h2 : p.height + 1 ≤ m.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h3 : (m.height : WithBot ℕ∞) ≤ ringKrullDim C := Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top
  rw [Ideal.height_bot, zero_add] at h1
  have h4 : (2 : ℕ∞) ≤ m.height := by
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ p.height + 1 := add_le_add h1 le_rfl
      _ ≤ m.height := h2
  have h5 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C := le_trans (by exact_mod_cast h4) h3
  have h6 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ 1 := le_trans h5 h
  exact absurd h6 (by decide)

theorem main
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (W : ValuationSubring F) (hW : IsDiscreteValuationRing ↥W) :
    ∃ V : ValuationSubring E, IsDiscreteValuationRing ↥V ∧
      (∀ x : F, x ∈ W → algebraMap F E x ∈ V) ∧
      (∀ x : ↥W, x ∈ maximalIdeal ↥W → algebraMap F E (x : F) ∈ V.nonunits) := by
  classical
  haveI := hW

  letI : Algebra ↥W E := ((algebraMap F E).comp (algebraMap ↥W F)).toAlgebra
  haveI : IsScalarTower ↥W F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hWE : ∀ x : ↥W, algebraMap ↥W E x = algebraMap F E (x : F) := fun _ => rfl
  have hinjWE : Function.Injective (algebraMap ↥W E) := by
    intro a b hab
    rw [hWE, hWE] at hab
    exact Subtype.ext ((algebraMap F E).injective hab)
  have hdim : ringKrullDim ↥W ≤ 1 := le_of_eq (IsDiscreteValuationRing.ringKrullDim_eq_one ↥W)
  have hnf : ¬ IsField ↥W := IsDiscreteValuationRing.not_isField ↥W

  set C : Subalgebra (↥W) E := integralClosure (↥W) E with hC
  obtain ⟨hCnoeth, hCdim⟩ := IsNoetherianRing.of_ringKrullDim_le_one_of_finiteDimensional_subalgebra hdim F E C
  haveI : IsNoetherianRing ↥C := hCnoeth
  haveI : IsFractionRing (↥C) E := integralClosure.isFractionRing_of_finite_extension F E
  haveI : Ring.DimensionLEOne ↥C := dimensionLEOne_of_ringKrullDim_le_one (↥C) hCdim
  haveI : IsIntegrallyClosedIn (↥C) E := IsIntegrallyClosedIn.of_isIntegralClosure (↥W)
  haveI : IsIntegrallyClosed ↥C := (isIntegrallyClosed_iff_isIntegrallyClosedIn E).mpr inferInstance
  haveI : IsDedekindRing ↥C := IsDedekindRing.mk
  haveI : IsDedekindDomain ↥C := IsDedekindDomain.mk
  have hinjWC : Function.Injective (algebraMap (↥W) (↥C)) := by
    intro a b hab
    apply hinjWE
    rw [IsScalarTower.algebraMap_apply (↥W) (↥C) E, hab, ← IsScalarTower.algebraMap_apply]
  have hker : RingHom.ker (algebraMap (↥W) (↥C)) ≤ maximalIdeal ↥W := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have : x = 0 := hinjWC (hx.trans (map_zero _).symm)
    rw [this]; exact zero_mem _
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := ↥C) (maximalIdeal ↥W) hker
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply hnf
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hQ, h]
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨fun hx => hinjWC (hx.trans (map_zero _).symm), fun hx => by rw [hx, map_zero]⟩
  haveI : Q.IsPrime := hQmax.isPrime
  let w : IsDedekindDomain.HeightOneSpectrum ↥C := ⟨Q, hQmax.isPrime, hQ0⟩
  set V := w.valuationSubringAtPrime E with hV
  haveI hlocV : IsLocalization.AtPrime (↥V) w.asIdeal :=
    IsDedekindDomain.HeightOneSpectrum.instIsLocalizationPrimeComplAsIdealSubtypeMemValuationSubringValuationSubringAtPrime w
  have k1 : ∀ c : ↥C, ((algebraMap (↥C) (↥V) c : ↥V) : E) = (c : E) := fun c =>
    (IsScalarTower.algebraMap_apply (↥C) (↥V) E c).symm
  have k2 : ∀ r : ↥W, ((algebraMap (↥W) (↥C) r : ↥C) : E) = algebraMap F E (r : F) := fun r => by
    rw [← hWE, IsScalarTower.algebraMap_apply (↥W) (↥C) E]; rfl
  refine ⟨V, ?_, ?_, ?_⟩
  · exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (↥C) (P := w.asIdeal) hQ0 _
  · intro x hx
    rw [← k2 ⟨x, hx⟩, ← k1]
    exact Subtype.mem _
  · intro x hx
    have e2 : algebraMap (↥W) (↥C) x ∈ w.asIdeal := by
      show algebraMap (↥W) (↥C) x ∈ Q
      rw [← Ideal.mem_comap, hQ]; exact hx
    have e3 := (IsLocalization.AtPrime.to_map_mem_maximal_iff (↥V) w.asIdeal (algebraMap (↥W) (↥C) x)).mpr e2
    rw [ValuationSubring.valuation_lt_one_iff, k1, k2] at e3
    exact (ValuationSubring.mem_nonunits_iff _).mpr e3

end DvrExtFinite

theorem solution
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (W : ValuationSubring F) (hW : IsDiscreteValuationRing ↥W) :
    ∃ V : ValuationSubring E, IsDiscreteValuationRing ↥V ∧
      (∀ x : F, x ∈ W → algebraMap F E x ∈ V) ∧
      (∀ x : ↥W, x ∈ maximalIdeal ↥W → algebraMap F E (x : F) ∈ V.nonunits) :=
  DvrExtFinite.main W hW

end S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional
end P2MW
export P2MW.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional (solution)
