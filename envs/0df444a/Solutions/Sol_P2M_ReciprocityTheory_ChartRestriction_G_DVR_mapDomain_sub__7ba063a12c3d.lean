-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_DVR_mapDomain_sub__7ba063a12c3d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:43.72162+00:00
-- url     : https://prove2.me/submissions/acbc9861-ac1e-46a3-964e-07dcfc53728c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection

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
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S}
variable {M : LB A.left}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {α β : Type} (f : α → β) (F G : α →₀ ℤ) :
    Finsupp.mapDomain f (F - G) = Finsupp.mapDomain f F - Finsupp.mapDomain f G := by
  exact map_sub (Finsupp.mapDomain.addMonoidHom f) F G
end ReciprocityTheory.ChartRestriction.G.DVR
