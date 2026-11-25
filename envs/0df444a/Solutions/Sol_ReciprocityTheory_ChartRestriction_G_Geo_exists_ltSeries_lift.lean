-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.exists_ltSeries_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:31.946143+00:00
-- url     : https://prove2.me/submissions/b8c78a5e-7f42-4d5c-8e09-f92a072bd50b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open Ideal
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ∀ (n : ℕ) (p : LTSeries (PrimeSpectrum R)), p.length = n →
      ∃ q : LTSeries (PrimeSpectrum S), q.length = n ∧
        q.last.asIdeal.comap (algebraMap R S) = p.last.asIdeal := by
  intro n
  induction n with
  | zero =>
    intro p _
    have hker : RingHom.ker (algebraMap R S) ≤ p.last.asIdeal := by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.last.asIdeal (⊥ : Ideal S)
      (by rw [← RingHom.ker_eq_comap_bot]; exact hker)
    exact ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, hQc⟩
  | succ n ih =>
    intro p hp
    obtain ⟨q', hq'len, hq'c⟩ := ih p.eraseLast (by
      first
      | (show p.length - 1 = n; omega)
      | simp [hp])
    have hlt : p.eraseLast.last < p.last := p.eraseLast_last_rel_last (by omega)
    obtain ⟨Q, hQle, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
      p.last.asIdeal q'.last.asIdeal (by rw [hq'c]; exact hlt.le)
    have hlt' : q'.last.asIdeal < Q := by
      refine lt_of_le_of_ne hQle fun h => hlt.ne ?_
      ext1
      rw [← hq'c, h, hQc]
    refine ⟨q'.snoc ⟨Q, hQ⟩ hlt', ?_, ?_⟩
    · show q'.length + 1 = n + 1
      rw [hq'len]
    · first
      | (rw [RelSeries.last_snoc]; exact hQc)
      | simpa using hQc
end ReciprocityTheory.ChartRestriction.G.Geo
