-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.lift_triple_comm_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:49:27.393976+00:00
-- url     : https://prove2.me/submissions/082f016c-a041-4798-b5f2-a8e7d00f31a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
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
theorem _root_.solution {T : Over S'} {T0 : Over S} (L : (Over.map m.e).obj T ⟶ T0) (p q r : T ⟶ G')
    (p0 q0 r0 : T0 ⟶ G) (hp : tb m p = L ≫ p0) (hq : tb m q = L ≫ q0) (hr : tb m r = L ≫ r0) :
    (lift p (lift q r)).left ≫ m.F3 = L.left ≫ (lift p0 (lift q0 r0)).left := by
  rw [cubeMapOf_thirdFace_eq_pushPt_lift]
  have h := congrArg (fun f => f.left) (tb_lift3 m p q r)
  simp only [Over.comp_left, Over.map_map_left] at h
  rw [h, hp, hq, hr, ← comp_lift, ← comp_lift, Over.comp_left]
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
