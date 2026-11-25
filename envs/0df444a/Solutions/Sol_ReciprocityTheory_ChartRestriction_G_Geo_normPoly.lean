-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.normPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:24:29.048814+00:00
-- url     : https://prove2.me/submissions/7445b500-4b54-4e65-8351-18c62ca1ddc7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeI
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeJ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_normPoly_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_pcMinContract


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution : NormPolyStatement := normPoly_of pcMinContract
end ReciprocityTheory.ChartRestriction.G.Geo
