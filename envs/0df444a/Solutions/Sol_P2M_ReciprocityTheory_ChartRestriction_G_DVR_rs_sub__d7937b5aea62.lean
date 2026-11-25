-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_DVR_rs_sub__d7937b5aea62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:55:16.771945+00:00
-- url     : https://prove2.me/submissions/694c8304-3351-48aa-af99-d0600b9f4a73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_MemFinsetInf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (x y : Γ(Z, U)) : rs h (x - y) = rs h x - rs h y := map_sub _ x y
end ReciprocityTheory.ChartRestriction.G.DVR
