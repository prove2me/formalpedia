-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.cube_face_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:09:06.63925+00:00
-- url     : https://prove2.me/submissions/5d09ecc5-15e7-4d92-9f17-047f6718c8c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_lift_triple_comm_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_pullback_proj_fourth

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi
variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  [IsCommMonObj G] (m : CubeMap G' G)
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf
theorem _root_.solution (a b c : Fin 4) :
    (lift (x4 G' a) (lift (x4 G' b) (x4 G' c))).left ≫ m.F3 =
      pullbackMapFourth m ≫ (lift (x4 G a) (lift (x4 G b) (x4 G c))).left := by
  rw [show pullbackMapFourth m = (L4 m).left from rfl,
    lift_triple_comm_pullback m (L4 m) _ _ _ _ _ _ (pullback_proj_fourth m a) (pullback_proj_fourth m b) (pullback_proj_fourth m c)]
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
