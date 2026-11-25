-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.cube_sum_face_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:10:36.083954+00:00
-- url     : https://prove2.me/submissions/fdc06f43-98b2-41fb-98ec-dcb26d2b1216

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_comp_padd__f5517b89e58c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_tb_padd
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
theorem _root_.solution (a b c d : Fin 4) :
    (lift (padd G' (x4 G' a) (x4 G' b)) (lift (x4 G' c) (x4 G' d))).left ≫ m.F3 =
      pullbackMapFourth m ≫ (lift (padd G (x4 G a) (x4 G b)) (lift (x4 G c) (x4 G d))).left := by
  have hp : tb m (padd G' (x4 G' a) (x4 G' b)) = L4 m ≫ padd G (x4 G a) (x4 G b) := by
    rw [tb_padd, pullback_proj_fourth, pullback_proj_fourth, comp_padd']
  rw [show pullbackMapFourth m = (L4 m).left from rfl,
    lift_triple_comm_pullback m (L4 m) _ _ _ _ _ _ hp (pullback_proj_fourth m c) (pullback_proj_fourth m d)]
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
