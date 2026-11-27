-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.UBC.eSec_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:28:49.701886+00:00
-- url     : https://prove2.me/submissions/78faf371-031e-4c83-8c80-709bf7c69ea1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_UnifBaseChangeInjOfSeamsCS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullbackDegree_EpsPullbackFst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_UBC_eps_pullback_fst

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
    eSec ((Over.pullback f).obj A) ≫ pullback.fst A.hom f = f ≫ eSec A := by
  simp only [eSec, Functor.obj.η_def, Over.comp_left, Category.assoc]
  erw [pullback.lift_fst]
  rw [← Category.assoc, eps_pullback_fst f]
end ReciprocityTheory.ChartRestriction.G.Out.UBC
