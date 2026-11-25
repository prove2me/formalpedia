-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_comp_pzero__45013db932d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:03.556166+00:00
-- url     : https://prove2.me/submissions/6dd143f0-204c-4e94-973c-4f22c44c723c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift

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
theorem _root_.solution {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] {T T' : Over S₀} (L : T' ⟶ T) :
    L ≫ pzero H T = pzero H T' := by
  first
    | simp [pzero]
    | (unfold pzero; simp)
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
