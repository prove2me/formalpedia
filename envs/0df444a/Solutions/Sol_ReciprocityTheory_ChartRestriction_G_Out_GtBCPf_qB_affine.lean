-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.qB_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:12:46.650282+00:00
-- url     : https://prove2.me/submissions/a7a00b8c-21d7-4f3d-9f2d-0b857c97bff6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PullbackSquarePartialSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_IBIsKernel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_qB_sq

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
theorem _root_.solution (h : IsAffineHom q.left) : IsAffineHom (qB f q).left :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (qB_sq f q) h
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
