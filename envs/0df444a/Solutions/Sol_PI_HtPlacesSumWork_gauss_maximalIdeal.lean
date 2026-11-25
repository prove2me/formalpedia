-- Prove2me | solution 1 for PI.HtPlacesSumWork.gauss_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:49:09.014722+00:00
-- url     : https://prove2.me/submissions/c052c2dc-95a1-41e2-b2f5-7074e8e86d88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_GaussMaximalIdeal
import Theorems.Thm_PI_HtPlacesSumWork_gauss_C_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
  (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
namespace PI.HtPlacesSumWork
theorem _root_.solution {π : 𝓞 K} (hπ : π ∈ la.asIdeal) {s : 𝓞 K} (hs : s ∉ la.asIdeal)
    (h : ∀ a ∈ la.asIdeal, ∃ b, s * a = π * b) :
    maximalIdeal (Op D N la) =
      Ideal.span {algebraMap (OT K D N) (Op D N la) (MvPolynomial.C π)} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := ReciprocityTheory.ChartRestriction.G.T0.laT D N la)]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    show Ideal.map (MvPolynomial.C : 𝓞 K →+* ReciprocityTheory.ChartRestriction.G.T0.OT K D N) la.asIdeal ≤ _
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_span_singleton']
    obtain ⟨b, hb⟩ := h a ha
    have hsP : (MvPolynomial.C s : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) ∈ (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl :=
      fun hm => hs ((gauss_C_mem_iff D N la s).mp hm)
    obtain ⟨u, hu⟩ := IsLocalization.map_units (S := ReciprocityTheory.ChartRestriction.G.T0.Op D N la)
      (⟨_, hsP⟩ : (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl)
    have key := congrArg (fun t => algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N)
      (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C t)) hb
    simp only [map_mul] at key
    have hu' : (u : ReciprocityTheory.ChartRestriction.G.T0.Op D N la) = algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N)
        (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C s) := hu
    refine ⟨(↑u⁻¹ : ReciprocityTheory.ChartRestriction.G.T0.Op D N la) * algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N)
      (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C b), ?_⟩
    symm
    calc algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C a)
        = (↑u⁻¹ : ReciprocityTheory.ChartRestriction.G.T0.Op D N la) * ((u : ReciprocityTheory.ChartRestriction.G.T0.Op D N la) *
          algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C a)) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [hu', key]; ring
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ ((gauss_C_mem_iff D N la π).mpr hπ)
end PI.HtPlacesSumWork
