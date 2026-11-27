-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.QForm.exists_rosati_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:22:18.545546+00:00
-- url     : https://prove2.me/submissions/293982c4-e0e6-4cac-bd35-f2e93f5c2f57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsRosatiGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_ros


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  (D : DegData V (maximalIdeal V))
variable {Q : D.toPre.X → ℤ}
namespace ReciprocityTheory.ChartRestriction.G.DVR.QForm
theorem _root_.solution (hLaws : Laws) {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] (ιD : D.OAct O) (a : O) :
    ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a))) rosatiε),
      u.IsGen ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (zero2 D.toPre.P.A))
        (LB.oneGen D.toPre.P.L) := by
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ros hLaws.globalFns D.toPre.P.isAb D.toPre.P.isLB _ _ (ιD.onB.rosati a)
end ReciprocityTheory.ChartRestriction.G.DVR.QForm
