-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.ratPrimeBelow_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:59.742055+00:00
-- url     : https://prove2.me/submissions/3a4b6f3b-6955-4e0b-9ced-108a3b653a20

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
theorem _root_.solution (𝔭 : HeightOneSpectrum (𝓞 K)) : (ratPrimeBelow 𝔭).Prime := by
  have hprime : (Ideal.span {((ratPrimeBelow 𝔭 : ℕ) : ℤ)}).IsPrime := by
    rw [← under_eq_span_ratPrimeBelow 𝔭]; exact (under_int_isMaximal 𝔭).isPrime
  have h0 : ((ratPrimeBelow 𝔭 : ℕ) : ℤ) ≠ 0 := by
    intro h
    apply under_int_ne_bot' 𝔭
    rw [under_eq_span_ratPrimeBelow 𝔭, h]
    exact Ideal.span_singleton_eq_bot.2 rfl
  rw [Nat.prime_iff_prime_int]
  exact (Ideal.span_singleton_prime h0).1 hprime
end ReciprocityTheory.Neutral.Bridge
