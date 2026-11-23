-- Prove2me | solution 1 for PI.HtPlacesSumWork.gauss_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:38.456747+00:00
-- url     : https://prove2.me/submissions/9b16e65b-f593-4dfe-95a6-f82d1194d06b

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
theorem _root_.solution (x : OT K D N) :
    OpToKT D N la (algebraMap (OT K D N) (Op D N la) x) =
      algebraMap (KTp K D N) (KTf K D N) (OTtoKT K D N x) := by
  rw [ReciprocityTheory.ChartRestriction.G.T0.OpToKT, IsLocalization.lift_eq, RingHom.comp_apply]
end PI.HtPlacesSumWork
