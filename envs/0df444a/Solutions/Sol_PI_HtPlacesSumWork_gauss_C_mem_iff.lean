-- Prove2me | solution 1 for PI.HtPlacesSumWork.gauss_C_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:43:28.524466+00:00
-- url     : https://prove2.me/submissions/59d94ebf-582e-4d41-9834-dccc926bfbf3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_GaussMaximalIdeal

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
theorem _root_.solution (s : 𝓞 K) :
    (MvPolynomial.C s : OT K D N) ∈ laT D N la ↔ s ∈ la.asIdeal := by
  constructor
  · intro h
    have h' : (MvPolynomial.C s : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) ∈
        Ideal.map (MvPolynomial.C : 𝓞 K →+* ReciprocityTheory.ChartRestriction.G.T0.OT K D N) la.asIdeal := h
    have h0 := (MvPolynomial.mem_map_C_iff.mp h') 0
    simpa using h0
  · intro h
    exact Ideal.mem_map_of_mem _ h
end PI.HtPlacesSumWork
