-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.iB_h
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:35:27.015836+00:00
-- url     : https://prove2.me/submissions/936b9cee-79b3-404a-b1f3-a48c3b4fb323

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PullbackSquarePartialSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_IBIsKernel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X]
variable {G B : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B)
variable (i : splitTorus S X ⟶ G)
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution : (iB f X i).left ≫ pullback.fst G.hom f = hT f X ≫ i.left := by
  unfold iB
  exact (isGrpPullback_pullback G f).1.lift_fst _ _ _
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
