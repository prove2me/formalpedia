-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.swap_first_two_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:13:16.485634+00:00
-- url     : https://prove2.me/submissions/e1f056b8-7d00-49c5-89d8-64ee5db82c7a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_cubeMapOf_thirdFace_eq_pushPt_lift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_lift_triple_comm_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_pullback_proj_cube

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
theorem _root_.solution :
    (lift (x3 G' 1) (lift (x3 G' 0) (x3 G' 2))).left ≫ m.F3 =
      m.F3 ≫ (lift (x3 G 1) (lift (x3 G 0) (x3 G 2))).left := by
  rw [lift_triple_comm_pullback m (L3 m) (x3 G' 1) (x3 G' 0) (x3 G' 2) (x3 G 1) (x3 G 0) (x3 G 2)
    (pullback_proj_cube m 1) (pullback_proj_cube m 0) (pullback_proj_cube m 2), cubeMapOf_thirdFace_eq_pushPt_lift]
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
