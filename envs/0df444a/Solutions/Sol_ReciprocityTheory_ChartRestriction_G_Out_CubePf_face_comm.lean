-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.face_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:13:13.987555+00:00
-- url     : https://prove2.me/submissions/420eba44-b774-495c-bdaf-f81a6ed3a4ed

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_lift_triple_comm_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_pullback_proj_square
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_tb_pzero__f3738fc98f21

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
theorem _root_.solution (i : Fin 3) :
    (faceMap G' i).left ≫ m.F3 = pullbackMapSquare m ≫ (faceMap G i).left := by
  fin_cases i
  · have h := lift_triple_comm_pullback m (L2 m) (pzero G' (G2 G')) (x2 G' 0) (x2 G' 1) (pzero G (G2 G)) (x2 G 0) (x2 G 1) (tb_pzero' m (L2 m)) (pullback_proj_square m 0) (pullback_proj_square m 1)
    first
      | exact h
      | (simp only [faceMap, pullbackMapSquare]; exact h)
      | simpa [faceMap, pullbackMapSquare] using h
  · have h := lift_triple_comm_pullback m (L2 m) (x2 G' 0) (pzero G' (G2 G')) (x2 G' 1) (x2 G 0) (pzero G (G2 G)) (x2 G 1) (pullback_proj_square m 0) (tb_pzero' m (L2 m)) (pullback_proj_square m 1)
    first
      | exact h
      | (simp only [faceMap, pullbackMapSquare]; exact h)
      | simpa [faceMap, pullbackMapSquare] using h
  · have h := lift_triple_comm_pullback m (L2 m) (x2 G' 0) (x2 G' 1) (pzero G' (G2 G')) (x2 G 0) (x2 G 1) (pzero G (G2 G)) (pullback_proj_square m 0) (pullback_proj_square m 1) (tb_pzero' m (L2 m))
    first
      | exact h
      | (simp only [faceMap, pullbackMapSquare]; exact h)
      | simpa [faceMap, pullbackMapSquare] using h
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
