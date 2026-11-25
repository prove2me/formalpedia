-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.mem_primesOverFinset_ratPrimeBelow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:30:38.787645+00:00
-- url     : https://prove2.me/submissions/5c68e561-92b4-42ce-8743-b817ec735286

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_ExistsPrimeAbsNormOfHasDirichletDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.Neutral.Bridge
open NumberField IsDedekindDomain Filter Topology
variable {K : Type*} [Field K] [NumberField K]
private theorem under_int_isMaximal (𝔭 : HeightOneSpectrum (𝓞 K)) : (𝔭.asIdeal.under ℤ).IsMaximal := by
  have := 𝔭.isMaximal
  exact Ideal.IsMaximal.under ℤ 𝔭.asIdeal
private theorem under_int_ne_bot' (𝔭 : HeightOneSpectrum (𝓞 K)) : 𝔭.asIdeal.under ℤ ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField (under_int_isMaximal 𝔭) Int.not_isField
private theorem int_ideal_eq_span_absNorm (J : Ideal ℤ) : J = Ideal.span {((Ideal.absNorm J : ℕ) : ℤ)} := by
  obtain ⟨a, rfl⟩ : ∃ a, J = Ideal.span {a} :=
    ⟨_, (Submodule.IsPrincipal.span_singleton_generator J).symm⟩
  rw [Ideal.absNorm_span_singleton]
  simp [Algebra.norm_self]
private theorem under_eq_span_ratPrimeBelow (𝔭 : HeightOneSpectrum (𝓞 K)) :
    𝔭.asIdeal.under ℤ = Ideal.span {((ratPrimeBelow 𝔭 : ℕ) : ℤ)} :=
  int_ideal_eq_span_absNorm _
end ReciprocityTheory.Neutral.Bridge
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open NumberField IsDedekindDomain Filter Topology
variable {K : Type*} [Field K] [NumberField K]
namespace ReciprocityTheory.Neutral.Bridge
theorem _root_.solution (𝔭 : HeightOneSpectrum (𝓞 K)) :
    𝔭.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {((ratPrimeBelow 𝔭 : ℕ) : ℤ)}) (𝓞 K) := by
  rw [← under_eq_span_ratPrimeBelow 𝔭]
  have := under_int_isMaximal 𝔭
  have := 𝔭.isMaximal
  have : 𝔭.asIdeal.IsPrime := 𝔭.isPrime
  rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset (under_int_ne_bot' 𝔭)]
  exact ⟨inferInstance, ⟨rfl⟩⟩
end ReciprocityTheory.Neutral.Bridge
