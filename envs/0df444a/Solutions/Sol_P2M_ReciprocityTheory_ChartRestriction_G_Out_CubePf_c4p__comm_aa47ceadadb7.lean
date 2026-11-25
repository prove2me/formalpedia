-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_c4p__comm_aa47ceadadb7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:09:00.605617+00:00
-- url     : https://prove2.me/submissions/27ad9510-8d94-4650-84f6-d5d7b1b1e24e

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
    (lift (x4 G' a) (lift (padd G' (x4 G' b) (x4 G' c)) (x4 G' d))).left ≫ m.F3 =
      pullbackMapFourth m ≫ (lift (x4 G a) (lift (padd G (x4 G b) (x4 G c)) (x4 G d))).left := by
  have hq : tb m (padd G' (x4 G' b) (x4 G' c)) = L4 m ≫ padd G (x4 G b) (x4 G c) := by
    rw [tb_padd, pullback_proj_fourth, pullback_proj_fourth, comp_padd']
  rw [show pullbackMapFourth m = (L4 m).left from rfl,
    lift_triple_comm_pullback m (L4 m) _ _ _ _ _ _ (pullback_proj_fourth m a) hq (pullback_proj_fourth m d)]
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
