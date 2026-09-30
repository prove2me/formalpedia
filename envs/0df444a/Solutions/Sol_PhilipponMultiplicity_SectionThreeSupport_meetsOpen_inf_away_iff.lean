-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.meetsOpen_inf_away_iff
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T12:13:26.025715+00:00
-- url     : https://prove2.me/submissions/1c9b63a1-4214-45d3-968a-07c0a786e206

import Definitions.Def_PhilipponMultiplicity_CutLocus
import Mathlib.RingTheory.Jacobson.Ring
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Pointwise
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- In this finite-type Jacobson ring, a prime meeting an open set also
meets its restriction away from any ideal not contained in that prime.
The witnessing maximal ideal may change. -/
theorem meetsOpen_inf_away_iff (q : Ideal M.CoordinateRing) (hq : q.IsPrime)
    (U : MaximalOpenLocus M) (A : Ideal M.CoordinateRing) :
    Hilbert.MeetsOpen K M.factorCount M.ambientDimension q (U ⊓ awayLocus M A) ↔
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U ∧ ¬ A ≤ q := by
  constructor
  · rintro ⟨m, ⟨hmU, hmA⟩, hqm⟩
    exact ⟨⟨m, hmU, hqm⟩, fun h => hmA (h.trans hqm)⟩
  · rintro ⟨⟨m, hmU, hqm⟩, hAq⟩
    obtain ⟨g, hgA, hgq⟩ := SetLike.not_le_iff_exists.mp hAq
    obtain ⟨V, hV, hUV⟩ := isOpen_induced_iff.mp U.isOpen
    have hmV : m.toPrimeSpectrum ∈ V := by
      change m ∈ MaximalSpectrum.toPrimeSpectrum ⁻¹' V
      rwa [hUV]
    obtain ⟨_, ⟨f, rfl⟩, hfm, hfV⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmV hV
    have hfq : f ∉ q := fun h => hfm (hqm h)
    have hfg : f * g ∉ q := fun h => (hq.mem_or_mem h).elim hfq hgq
    have hj : q.jacobson = q := isJacobsonRing_iff_prime_eq.mp inferInstance q hq
    obtain ⟨n, ⟨hqn, hn⟩, hfgn⟩ := Ideal.eq_jacobson_iff_notMem.mp hj (f * g) hfg
    have hfn : f ∉ n := fun h => hfgn (n.mul_mem_right g h)
    have hgn : g ∉ n := fun h => hfgn (n.mul_mem_left f h)
    refine ⟨⟨n, hn⟩, ⟨?_, ?_⟩, hqn⟩
    · change (⟨n, hn⟩ : MaximalSpectrum M.CoordinateRing) ∈
        (U : Set (MaximalSpectrum M.CoordinateRing))
      rw [← hUV]
      exact hfV hfn
    · exact fun hAn => hgn (hAn hgA)

end PhilipponMultiplicity.SectionThreeSupport

end

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (q : Ideal M.CoordinateRing) (hq : q.IsPrime)
    (U : MaximalOpenLocus M) (A : Ideal M.CoordinateRing) :
    Hilbert.MeetsOpen K M.factorCount M.ambientDimension q (U ⊓ awayLocus M A) ↔
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U ∧ ¬ A ≤ q := by
  exact PhilipponMultiplicity.SectionThreeSupport.meetsOpen_inf_away_iff M q hq U A
