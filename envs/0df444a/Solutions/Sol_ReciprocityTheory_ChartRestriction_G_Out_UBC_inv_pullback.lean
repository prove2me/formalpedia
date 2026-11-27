-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.UBC.inv_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:29:00.71098+00:00
-- url     : https://prove2.me/submissions/7ca74677-b5b4-4805-84e8-95f0ad696098

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_UnifBaseChangeInjOfSeamsCS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullbackDegree_EpsPullbackFst

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.UBC
open Semi
namespace ReciprocityTheory.ChartRestriction.G.Out.UBC
theorem _root_.solution {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A] :
    (ι[(Over.pullback f).obj A]).left ≫ pullback.fst A.hom f = pullback.fst A.hom f ≫ (ι[A]).left := by
  simp [Functor.obj.ι_def]
  exact pullback.lift_fst _ _ _
end ReciprocityTheory.ChartRestriction.G.Out.UBC
