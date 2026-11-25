-- Prove2me | solution 1 for PI.HtPlacesSumWork.gauss_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:58:38.799701+00:00
-- url     : https://prove2.me/submissions/2c16a4be-1b4b-40a6-b852-348915cbd17d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_GaussMaximalIdeal
import Theorems.Thm_PI_HtPlacesSumWork_gauss_unif
import Theorems.Thm_PI_HtPlacesSumWork_gauss_inj
import Theorems.Thm_PI_HtPlacesSumWork_gauss_maximalIdeal

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
theorem _root_.solution : IsDiscreteValuationRing (Op D N la) := by
  obtain ⟨π, hπ, hπ0, s, hs, h⟩ := gauss_unif la
  have hmax := gauss_maximalIdeal D N la hπ hs h
  have : IsDomain (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
  have : IsNoetherianRing (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) :=
    IsLocalization.isNoetherianRing (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl _ inferInstance
  have hne : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)
      (MvPolynomial.C π) ≠ 0 := by
    intro h0
    apply hπ0
    have h1 := gauss_inj D N la (h0.trans (map_zero _).symm)
    simpa using h1
  have hnf : ¬ IsField (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) := by
    intro hF
    have hmem : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)
        (MvPolynomial.C π) ∈ maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) := by
      rw [hmax]; exact Ideal.mem_span_singleton_self _
    obtain ⟨y, hy⟩ := hF.mul_inv_cancel hne
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem (isUnit_iff_exists_inv.mpr ⟨y, hy⟩)
  have hprin : (maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)).IsPrincipal := ⟨⟨_, hmax⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) hnf).out 0 4).mpr hprin
end PI.HtPlacesSumWork
