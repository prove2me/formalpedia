-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.tb_padd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:50:47.969477+00:00
-- url     : https://prove2.me/submissions/3967a513-6459-412f-ae9f-fc991be1e244

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_tb_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_psum_01
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_comp_padd__f5517b89e58c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_cubeMapOf_thirdFace_eq_pushPt_lift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_tb_lift3

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
theorem _root_.solution {T : Over S'} (y z : T ⟶ G') : tb m (padd G' y z) = padd G (tb m y) (tb m z) := by
  ext
  have hw : lift y (lift z y) ≫ padd G' (x3 G' 0) (x3 G' 1) = padd G' y z := by
    simp [comp_padd', x3]
  have h01 := m.psum_comm {0, 1}
  rw [psum_01, psum_01] at h01
  have h3 := congrArg (fun f => f.left) (tb_lift3 m y z y)
  simp only [Over.comp_left, Over.map_map_left] at h3
  rw [tb_left, ← hw, Over.comp_left, Category.assoc, h01, cubeMapOf_thirdFace_eq_pushPt_lift, ← Category.assoc, h3,
    ← Over.comp_left, comp_padd']
  simp [x3]
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
