-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.finite_height_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:17:18.340112+00:00
-- url     : https://prove2.me/submissions/e09e5337-8c12-4701-90e4-a8fd53190b77

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.Integer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_MemRangeOfForallHeightOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]
omit [IsFractionRing A K]
namespace ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
theorem _root_.solution [IsNoetherianRing A] {a : A} (ha : a ≠ 0) :
    {P : Ideal A | P.IsPrime ∧ P.height = 1 ∧ a ∈ P}.Finite := by
  classical
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})).subset ?_
  rintro P ⟨hP, h1, haP⟩
  have hle : Ideal.span {a} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr haP
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hle
  have hQprime : Q.IsPrime := hQ.1.1
  by_cases hQP' : Q = P
  · exact hQP' ▸ hQ
  · exfalso
    have hlt : Q < P := lt_of_le_of_ne hQP hQP'
    have hQne : (⊥ : Ideal A) < Q := by
      refine lt_of_le_of_ne bot_le (fun hb => ha ?_)
      have h3 : a ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self a)
      rw [← hb] at h3
      exact Ideal.mem_bot.mp h3
    have h1' : Order.height (⟨P, hP⟩ : PrimeSpectrum A) = 1 := by
      first
      | (rw [Ideal.IsPrime.height_eq_primeHeight] at h1; exact h1)
      | (rw [Ideal.height_eq_primeHeight_of_isPrime] at h1; exact h1)
      | (rw [← Ideal.primeHeight_eq_height] at h1; exact h1)
      | (rw [Ideal.IsPrime.height] at h1; exact h1)
      | (simp only [Ideal.height, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff,
          iInf_iInf_eq_left] at h1; exact h1)
    have hlt' : (⟨Q, hQprime⟩ : PrimeSpectrum A) < ⟨P, hP⟩ := (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp hlt
    have hQ1 : Order.height (⟨Q, hQprime⟩ : PrimeSpectrum A) < 1 := by
      rw [← h1']
      exact Order.height_strictMono hlt'
        (lt_of_le_of_lt (Order.height_mono (le_of_lt hlt')) (by rw [h1']; exact ENat.one_lt_top))
    have hne' : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum A) < ⟨Q, hQprime⟩ :=
      (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp hQne
    have hQ0 := Order.height_strictMono hne'
      (lt_of_le_of_lt (Order.height_mono (le_of_lt hne')) (lt_trans hQ1 ENat.one_lt_top))
    have hQz : Order.height (⟨Q, hQprime⟩ : PrimeSpectrum A) = 0 := ENat.lt_one_iff_eq_zero.mp hQ1
    rw [hQz] at hQ0
    exact absurd hQ0 (not_lt_zero')
end ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
