-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.card_primesOverFinset_span_le_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:49:43.909289+00:00
-- url     : https://prove2.me/submissions/c71f7ed4-2364-49bb-9d70-d4a677a7445a

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
private theorem span_natCast_isMaximal_of_prime (p : ℕ) (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal := by
  exact PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
end ReciprocityTheory.Neutral.Bridge
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open NumberField IsDedekindDomain Filter Topology
variable {K : Type*} [Field K] [NumberField K]
namespace ReciprocityTheory.Neutral.Bridge
theorem _root_.solution (p : ℕ) (hp : p.Prime) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K)).card ≤ Module.finrank ℚ K := by
  have := span_natCast_isMaximal_of_prime p hp
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  have hsum := Ideal.sum_ramification_inertia (p := Ideal.span {(p : ℤ)}) (S := 𝓞 K) ℚ K hp0
  rw [← hsum, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro P hP
  rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hp0] at hP
  obtain ⟨hPp, hPo⟩ := hP
  have hle : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ P := by
    exact Ideal.map_le_of_le_comap (le_of_eq hPo.over)
  have he : (Ideal.span {(p : ℤ)}).ramificationIdx' P ≠ 0 := by
    exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero (Ideal.map_ne_bot_of_ne_bot hp0) hPp hle
  have hf : (Ideal.span {(p : ℤ)}).inertiaDeg' P ≠ 0 := by
    exact (Ideal.inertiaDeg'_pos (Ideal.span {(p : ℤ)}) P).ne'
  exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero he hf)
end ReciprocityTheory.Neutral.Bridge
