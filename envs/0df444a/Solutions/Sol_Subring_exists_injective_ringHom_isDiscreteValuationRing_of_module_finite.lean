-- Prove2me | solution 1 for Subring.exists_injective_ringHom_isDiscreteValuationRing_of_module_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9fa66b3e-27a1-5026-b1c4-7f17f2065267

import Definitions.Def_NumberField_Completion_HenselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subring_exists_injective_ringHom_isDiscreteValuationRing_of_module_finite

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace S2aKLeg

theorem exists_numberField_leg (A : Subring ℂ) [Module.Finite ℤ A] (l : ℕ) [hl : Fact l.Prime] :
    ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField ↥K) (f : A →+* 𝓞 ↥K)
      (v : HeightOneSpectrum (𝓞 ↥K)),
      Function.Injective ⇑f ∧ (l : 𝓞 ↥K) ∈ v.asIdeal := by
  classical
  obtain ⟨s, hs⟩ : (⊤ : Submodule ℤ A).FG := Module.Finite.fg_top
  have hint : ∀ a : A, IsIntegral ℤ (a : ℂ) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) a).map A.subtype.toIntAlgHom
  set S : Set ℂ := (fun a : A => (a : ℂ)) '' (↑s : Set A) with hSdef
  have hSfin : S.Finite := s.finite_toSet.image _
  set K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ S with hKdef
  haveI : Finite ↥S := hSfin.to_subtype
  haveI hKfd : FiniteDimensional ℚ ↥K :=
    IntermediateField.finiteDimensional_adjoin fun x hx => by
      obtain ⟨a, -, rfl⟩ := hx
      exact (hint a).tower_top
  haveI hKnf : NumberField ↥K := ⟨⟩
  have hmem : ∀ a : A, (a : ℂ) ∈ K := by
    have hsub : (fun a : A => (a : ℂ)) '' (↑s : Set A) ⊆ (K : Set ℂ) := fun x hx =>
      IntermediateField.subset_adjoin ℚ S hx
    have hle : Submodule.span ℤ ((fun a : A => (a : ℂ)) '' (↑s : Set A)) ≤
        Submodule.restrictScalars ℤ (Subalgebra.toSubmodule K.toSubalgebra) :=
      Submodule.span_le.mpr hsub
    intro a
    have ha : a ∈ Submodule.span ℤ (↑s : Set A) := hs ▸ Submodule.mem_top
    have hmap := Submodule.mem_map_of_mem (f := A.subtype.toIntAlgHom.toLinearMap) ha
    rw [Submodule.map_span] at hmap
    exact hle hmap
  let g : A →+* ↥K := A.subtype.codRestrict K hmem
  have hgint : ∀ a : A, IsIntegral ℤ (g a) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) a).map g.toIntAlgHom
  let f : A →+* 𝓞 ↥K :=
    { toFun := fun a => ⟨g a, hgint a⟩
      map_one' := Subtype.ext (map_one g)
      map_mul' := fun a b => Subtype.ext (map_mul g a b)
      map_zero' := Subtype.ext (map_zero g)
      map_add' := fun a b => Subtype.ext (map_add g a b) }
  have hfval : ∀ a : A, ((f a : ↥K) : ℂ) = (a : ℂ) := fun a => rfl
  have finj : Function.Injective ⇑f := by
    intro a b hab
    have h1 := congrArg (fun t : 𝓞 ↥K => ((t : ↥K) : ℂ)) hab
    simp only [hfval] at h1
    exact Subtype.coe_injective h1
  have hp : Prime ((l : ℕ) : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using hl.out
  haveI hPprime : (Ideal.span {((l : ℕ) : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).mpr hp
  have hinj : Function.Injective (algebraMap ℤ (𝓞 ↥K)) := fun m n h => by
    simpa using h
  have hker : RingHom.ker (algebraMap ℤ (𝓞 ↥K)) ≤ Ideal.span {((l : ℕ) : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨Q, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (R := ℤ) (S := 𝓞 ↥K)
      (Ideal.span {((l : ℕ) : ℤ)}) hker
  have hlQ : (l : 𝓞 ↥K) ∈ Q := by
    have h1 : ((l : ℕ) : ℤ) ∈ Ideal.span {((l : ℕ) : ℤ)} := Ideal.mem_span_singleton_self _
    rw [← hQcomap] at h1
    have h2 : algebraMap ℤ (𝓞 ↥K) ((l : ℕ) : ℤ) ∈ Q := h1
    simpa using h2
  have hQne : Q ≠ ⊥ := by
    intro hbot
    rw [hbot] at hQcomap
    have hc : Ideal.comap (algebraMap ℤ (𝓞 ↥K)) (⊥ : Ideal (𝓞 ↥K)) = ⊥ :=
      Ideal.comap_bot_of_injective _ hinj
    rw [hc] at hQcomap
    have : ((l : ℕ) : ℤ) = 0 := Ideal.span_singleton_eq_bot.mp hQcomap.symm
    exact hl.out.ne_zero (by exact_mod_cast this)
  exact ⟨K, hKnf, f, ⟨Q, hQprime, hQne⟩, finj, hlQ⟩

theorem exists_numberField_ringOfIntegers_heightOne (A : Subring ℂ) [Module.Finite ℤ A]
    (l : ℕ) [Fact l.Prime] :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (f : A →+* 𝓞 K)
      (v : HeightOneSpectrum (𝓞 K)),
      Function.Injective ⇑f ∧ (l : 𝓞 K) ∈ v.asIdeal := by
  obtain ⟨K, hKnf, f, v, hfinj, hlv⟩ := exists_numberField_leg A l
  exact ⟨↥K, inferInstance, hKnf, f, v, hfinj, hlv⟩

end S2aKLeg

theorem solution (A : Subring ℂ) [Module.Finite ℤ A] (l : ℕ) [Fact l.Prime] :
    ∃ (𝓞' : Type) (_ : CommRing 𝓞') (_ : IsDomain 𝓞') (_ : IsDiscreteValuationRing 𝓞')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝓞') 𝓞')
      (_ : Finite (IsLocalRing.ResidueField 𝓞')) (_ : CharZero 𝓞'),
      (l : 𝓞') ∈ IsLocalRing.maximalIdeal 𝓞' ∧ ∃ ι : A →+* 𝓞', Function.Injective ι := by
  obtain ⟨K, _, hKnf, f, v, hfinj, hlv⟩ := S2aKLeg.exists_numberField_ringOfIntegers_heightOne A l
  haveI hCZcompl : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  refine ⟨↥(v.adicCompletionIntegers K), inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  ·
    have h1 : (l : ↥(v.adicCompletionIntegers K)) =
        algebraMap (𝓞 K) (v.adicCompletionIntegers K) (l : 𝓞 K) := by simp
    rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    change ¬ Valued.v (((algebraMap (𝓞 K) K) (l : 𝓞 K) : K) : v.adicCompletion K) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap]
    exact ne_of_lt ((HeightOneSpectrum.intValuation_lt_one_iff_mem v (l : 𝓞 K)).mpr hlv)
  · refine ⟨(algebraMap (𝓞 K) (v.adicCompletionIntegers K)).comp f, ?_⟩
    have h2 : Function.Injective (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) :=
      FaithfulSMul.algebraMap_injective _ _
    rw [RingHom.coe_comp]
    exact h2.comp hfinj

end S_Subring_exists_injective_ringHom_isDiscreteValuationRing_of_module_finite
end P2MW
export P2MW.S_Subring_exists_injective_ringHom_isDiscreteValuationRing_of_module_finite (solution)
