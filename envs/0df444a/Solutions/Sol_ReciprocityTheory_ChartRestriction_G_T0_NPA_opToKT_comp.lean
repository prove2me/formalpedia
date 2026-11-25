-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPA.opToKT_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:07:17.592471+00:00
-- url     : https://prove2.me/submissions/58455162-3f8c-4776-89e4-1bea0ba0a3bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPtsA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.NPA
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
  (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
namespace ReciprocityTheory.ChartRestriction.G.T0.NPA
theorem _root_.solution : (OpToKT D N la).comp (algebraMap (OT K D N) (Op D N la)) =
    (algebraMap (KTp K D N) (KTf K D N)).comp (OTtoKT K D N) := by
  unfold OpToKT
  exact IsLocalization.lift_comp _
end ReciprocityTheory.ChartRestriction.G.T0.NPA
