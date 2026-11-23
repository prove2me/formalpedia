-- Prove2me | solution 1 for PI.HtPlacesSumWork.gauss_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:25.428431+00:00
-- url     : https://prove2.me/submissions/d70bb1b9-bba4-47a1-956f-063ccbcd497a

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
theorem _root_.solution : Function.Injective (algebraMap (OT K D N) (Op D N la)) :=
  IsLocalization.injective (M := (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl)
    (S := ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (Ideal.primeCompl_le_nonZeroDivisors _)
end PI.HtPlacesSumWork
