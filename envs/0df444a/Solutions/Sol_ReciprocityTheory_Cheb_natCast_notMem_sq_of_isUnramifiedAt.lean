-- Prove2me | solution 1 for ReciprocityTheory.Cheb.natCast_notMem_sq_of_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:59.888072+00:00
-- url     : https://prove2.me/submissions/497668d5-4ab0-4847-b8cc-c43394e2a7e2

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CyclotomicIrreducibleOfForallIsUnramifiedAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Cheb
open Polynomial NumberField
namespace ReciprocityTheory.Cheb
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {l : ℕ}
    (hl : l.Prime) (P : Ideal (𝓞 K)) [P.IsPrime]
    [Algebra.IsUnramifiedAt ℤ P] : (l : 𝓞 K) ∉ P ^ 2 := by
  intro hl2
  have hlP : (l : 𝓞 K) ∈ P := Ideal.pow_le_self two_ne_zero hl2
  have hl0 : (l : 𝓞 K) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hP0 : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hlP
    exact hl0 hlP
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hle : Ideal.span {(l : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    simpa [Ideal.under, Ideal.mem_comap] using hlP
  have hunder : Ideal.span {(l : ℤ)} = P.under ℤ :=
    hmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top hle
  haveI : P.LiesOver (Ideal.span {(l : ℤ)}) := ⟨hunder⟩
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(l : ℤ)}) = Ideal.span {(l : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hmap0 : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(l : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact hl0
  have hcount := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    (Ideal.span {(l : ℤ)}) P hmap0
  rw [Ideal.ramificationIdx_eq_one_of_isUnramifiedAt] at hcount

  have hdvd : P ^ 2 ∣ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(l : ℤ)}) := by
    rw [Ideal.dvd_iff_le, hmap, Ideal.span_le, Set.singleton_subset_iff]
    exact hl2
  have hP2 : P ^ 2 ≠ 0 := pow_ne_zero _ (by simpa using hP0)
  have hnf := (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP2
    (by simpa using hmap0)).mp hdvd
  have hc := Multiset.count_le_of_le P hnf
  rw [← hcount, UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_irreducible (Ideal.prime_of_isPrime hP0 inferInstance).irreducible,
    normalize_eq] at hc
  simp at hc
end ReciprocityTheory.Cheb
