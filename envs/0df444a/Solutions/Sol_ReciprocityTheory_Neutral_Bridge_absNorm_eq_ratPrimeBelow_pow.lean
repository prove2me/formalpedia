-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.absNorm_eq_ratPrimeBelow_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:36:19.7263+00:00
-- url     : https://prove2.me/submissions/1a035aae-17db-4347-a195-7905462672d2

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_ExistsPrimeAbsNormOfHasDirichletDensity
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_ratPrimeBelow_prime
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
private theorem int_ideal_eq_span_absNorm (J : Ideal ℤ) : J = Ideal.span {((Ideal.absNorm J : ℕ) : ℤ)} := by
  obtain ⟨a, rfl⟩ : ∃ a, J = Ideal.span {a} :=
    ⟨_, (Submodule.IsPrincipal.span_singleton_generator J).symm⟩
  rw [Ideal.absNorm_span_singleton]
  simp [Algebra.norm_self]
private theorem under_eq_span_ratPrimeBelow (𝔭 : HeightOneSpectrum (𝓞 K)) :
    𝔭.asIdeal.under ℤ = Ideal.span {((ratPrimeBelow 𝔭 : ℕ) : ℤ)} :=
  int_ideal_eq_span_absNorm _
private theorem natCast_ratPrimeBelow_mem (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ((ratPrimeBelow 𝔭 : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal := by
  have h1 : ((ratPrimeBelow 𝔭 : ℕ) : ℤ) ∈ 𝔭.asIdeal.under ℤ := by
    rw [under_eq_span_ratPrimeBelow 𝔭]; exact Ideal.subset_span rfl
  have h2 : algebraMap ℤ (𝓞 K) ((ratPrimeBelow 𝔭 : ℕ) : ℤ) ∈ 𝔭.asIdeal := h1
  simpa using h2
private theorem absNorm_span_natCast_eq_pow_finrank (p : ℕ) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ Module.finrank ℚ K := by
  rw [Ideal.absNorm_span_singleton]
  have : ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) ((p : ℕ) : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
  simp [Int.natAbs_pow]
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
    ∃ f : ℕ, Ideal.absNorm 𝔭.asIdeal = ratPrimeBelow 𝔭 ^ f := by
  have hp := ratPrimeBelow_prime 𝔭
  have hle : Ideal.span {((ratPrimeBelow 𝔭 : ℕ) : 𝓞 K)} ≤ 𝔭.asIdeal :=
    Ideal.span_le.2 (Set.singleton_subset_iff.2 (natCast_ratPrimeBelow_mem 𝔭))
  have hdvd : Ideal.absNorm 𝔭.asIdeal ∣ Ideal.absNorm (Ideal.span {((ratPrimeBelow 𝔭 : ℕ) : 𝓞 K)}) := by
    exact Ideal.absNorm_dvd_absNorm_of_le hle
  rw [absNorm_span_natCast_eq_pow_finrank] at hdvd
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  exact ⟨f, hf⟩
end ReciprocityTheory.Neutral.Bridge
