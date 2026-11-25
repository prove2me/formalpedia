-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_tb_pzero__f3738fc98f21
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:59.175967+00:00
-- url     : https://prove2.me/submissions/b0b5e848-1604-4e09-a924-b66c38beefb7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_tb_pzero
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_comp_pzero__45013db932d5

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
theorem _root_.solution {T : Over S'} {T0 : Over S} (L : (Over.map m.e).obj T ⟶ T0) :
    tb m (pzero G' T) = L ≫ pzero G T0 := by
  rw [tb_pzero, comp_pzero']
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
