-- Prove2me | solution 1 for ReciprocityTheory.Cheb.exists_forall_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:55.20345+00:00
-- url     : https://prove2.me/submissions/7a5916b4-9850-4d81-8ee3-ad2f3e1ae51b

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CyclotomicIrreducibleOfForallIsUnramifiedAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.Cheb
open Polynomial NumberField
private theorem setOf_prime_ramified_finite (K : Type*) [Field K] [NumberField K] :
    {p : ℕ | p.Prime ∧ ∃ (P : Ideal (𝓞 K)) (_ : P.IsPrime), (p : 𝓞 K) ∈ P ∧
      ¬ Algebra.IsUnramifiedAt ℤ P}.Finite := by
  have hD : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hF := Ideal.finite_factors (I := differentIdeal ℤ (𝓞 K)) (by simpa using hD)

  have hsub : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      {p : ℕ | p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal}.Subsingleton := by
    intro v p ⟨hp, hpv⟩ q ⟨hq, hqv⟩
    by_contra hne
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
    have hc : IsCoprime (p : 𝓞 K) (q : 𝓞 K) := by
      have := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom (𝓞 K))
      simpa using this
    obtain ⟨a, b, hab⟩ := hc
    have h1 : (1 : 𝓞 K) ∈ v.asIdeal := hab ▸
      v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hpv) (v.asIdeal.mul_mem_left b hqv)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  refine (hF.biUnion (fun v _ => (hsub v).finite)).subset ?_
  rintro p ⟨hp, P, hPp, hpP, hnr⟩
  have hP0 : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  exact Set.mem_biUnion (x := ⟨P, hPp, hP0⟩) (dvd_differentIdeal_iff.mpr hnr) ⟨hp, hpP⟩
end ReciprocityTheory.Cheb
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Cheb
open Polynomial NumberField
namespace ReciprocityTheory.Cheb
theorem _root_.solution (K : Type*) [Field K] [NumberField K] :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → N < p → ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (p : 𝓞 K) ∈ P →
      Algebra.IsUnramifiedAt ℤ P := by
  obtain ⟨N, hN⟩ := (setOf_prime_ramified_finite K).bddAbove
  refine ⟨N, fun p hp hpN P _ hpP => ?_⟩
  by_contra h
  exact absurd (hN ⟨hp, P, inferInstance, hpP, h⟩) (not_le.mpr hpN)
end ReciprocityTheory.Cheb
