-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.succ_le_ringKrullDim_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:21.618336+00:00
-- url     : https://prove2.me/submissions/227a4f55-6384-442d-9b89-950877414d00

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
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B]
    (hext : ∀ p : Ideal A, p.IsPrime → Disjoint (M : Set A) p → ∃ q : Ideal A, q.IsPrime ∧ p < q)
    (n : ℕ) (h : (n : WithBot ℕ∞) ≤ ringKrullDim B) :
    ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim A := by
  let φ : PrimeSpectrum B → PrimeSpectrum A := fun q => ⟨q.asIdeal.comap (algebraMap A B), inferInstance⟩
  have hsm : StrictMono φ := fun a b hab => by
    refine lt_of_le_of_ne (Ideal.comap_mono hab.le) fun e => hab.ne ?_
    have e' : (φ a).asIdeal = (φ b).asIdeal := congrArg PrimeSpectrum.asIdeal e
    ext1
    rw [← IsLocalization.map_comap M B a.asIdeal, ← IsLocalization.map_comap M B b.asIdeal]
    exact congrArg (Ideal.map (algebraMap A B)) e'
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp h
  let p' := p.map φ hsm
  have hdisj : Disjoint (M : Set A) (p'.last.asIdeal : Set A) :=
    ((IsLocalization.isPrime_iff_isPrime_disjoint M B p.last.asIdeal).mp inferInstance).2
  obtain ⟨q, hq, hlt⟩ := hext p'.last.asIdeal inferInstance hdisj
  have hlen : (p'.snoc ⟨q, hq⟩ hlt).length = n + 1 := by
    show p.length + 1 = n + 1
    rw [hp]
  exact Order.le_krullDim_iff.mpr ⟨_, hlen⟩
end ReciprocityTheory.ChartRestriction.G.Geo
