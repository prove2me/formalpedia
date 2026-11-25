-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.qB_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:51:41.846688+00:00
-- url     : https://prove2.me/submissions/5c313504-b59e-4d3f-a59e-55bdc182533b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PullbackSquarePartialSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_IBIsKernel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_qB_h
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution : IsPullback (pullback.fst G.hom f) (qB f q).left q.left (pullback.fst B.hom f) := by
  refine IsPullback.of_bot ?_ (qB_h f q).symm (IsPullback.of_hasPullback B.hom f)
  have e1 : (qB f q).left ≫ pullback.snd B.hom f = pullback.snd G.hom f := by
    simp [qB]
    exact pullback.lift_snd _ _ _
  have e2 : q.left ≫ B.hom = G.hom := Over.w q
  rw [e1, e2]
  exact IsPullback.of_hasPullback G.hom f
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
