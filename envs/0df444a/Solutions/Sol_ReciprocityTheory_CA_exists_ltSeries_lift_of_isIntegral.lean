-- Prove2me | solution 1 for ReciprocityTheory.CA.exists_ltSeries_lift_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:19.600743+00:00
-- url     : https://prove2.me/submissions/78abefdf-3dce-42b8-944c-a37f1ebf6e8e

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.CA
private theorem exists_prime_over_lemma {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (p : Ideal A) [p.IsPrime] (I : Ideal B)
    (hI : I.comap (algebraMap A B) ≤ p) :
    ∃ Q : Ideal B, I ≤ Q ∧ Q.IsPrime ∧ Q.comap (algebraMap A B) = p := by
  first
  | exact Ideal.exists_ideal_over_prime_of_isIntegral p I hI
  | exact Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime p I hI
  | (obtain ⟨Q, h1, h2, h3⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p I hI
     exact ⟨Q, h1, h2, h3⟩)
end ReciprocityTheory.CA
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
namespace ReciprocityTheory.CA
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (h : Function.Injective (algebraMap A B))
    (l : LTSeries (PrimeSpectrum A)) :
    ∃ l' : LTSeries (PrimeSpectrum B), l'.length = l.length ∧
      l'.last.asIdeal.comap (algebraMap A B) = l.last.asIdeal := by
  suffices H : ∀ n, ∀ l : LTSeries (PrimeSpectrum A), l.length = n →
      ∃ l' : LTSeries (PrimeSpectrum B), l'.length = l.length ∧
        l'.last.asIdeal.comap (algebraMap A B) = l.last.asIdeal by
    exact H _ l rfl
  intro n
  induction n with
  | zero =>
    intro l hl
    obtain ⟨Q, -, hQ, hQc⟩ := exists_prime_over_lemma l.last.asIdeal ⊥ (by
      first
      | (rw [Ideal.comap_bot_of_injective _ h]; exact bot_le)
      | (intro y hy
         rw [Ideal.mem_comap, Ideal.mem_bot] at hy
         rw [show y = 0 from h (by rw [hy, map_zero])]
         exact Ideal.zero_mem _))
    refine ⟨RelSeries.singleton _ ⟨Q, hQ⟩, ?_, ?_⟩
    · simp [hl]
    · simpa using hQc
  | succ n ih =>
    intro l hl
    have hne : l.length ≠ 0 := by omega
    obtain ⟨l', hlen, hlast⟩ := ih l.eraseLast (by simp [hl])
    have hlt : l.eraseLast.last < l.last := l.eraseLast_last_rel_last hne
    obtain ⟨Q, hQle, hQ, hQc⟩ := exists_prime_over_lemma l.last.asIdeal l'.last.asIdeal (by
      rw [hlast]
      exact le_of_lt hlt)
    have hlt' : l'.last < ⟨Q, hQ⟩ := by
      refine lt_of_le_of_ne hQle ?_
      intro heq
      have hc := congrArg (fun q : PrimeSpectrum B => q.asIdeal.comap (algebraMap A B)) heq
      simp only at hc
      rw [hlast, hQc] at hc
      exact (ne_of_lt hlt) (PrimeSpectrum.ext hc)
    refine ⟨l'.snoc ⟨Q, hQ⟩ hlt', ?_, ?_⟩
    · first
      | (simp [hlen, hl]; done)
      | (simp [hlen, hl]; omega)
    · simpa using hQc
end ReciprocityTheory.CA
