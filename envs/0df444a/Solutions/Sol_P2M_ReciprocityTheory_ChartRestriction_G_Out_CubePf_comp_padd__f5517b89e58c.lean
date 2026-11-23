-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_comp_padd__f5517b89e58c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:54.13185+00:00
-- url     : https://prove2.me/submissions/a391975e-a076-4470-8267-0fa8c741f2d4

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
theorem _root_.solution {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] {T T' : Over S₀} (L : T' ⟶ T)
    (a b : T ⟶ H) : L ≫ padd H a b = padd H (L ≫ a) (L ≫ b) := by
  first
    | (simp only [padd, ← Category.assoc, CartesianMonoidalCategory.comp_lift])
    | (unfold padd; rw [← Category.assoc, CartesianMonoidalCategory.comp_lift])
    | simp [padd]
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
