-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.UBC.homEquiv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:22.628906+00:00
-- url     : https://prove2.me/submissions/85eaa625-5c89-4668-a3bf-9a7123ea27d9

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
theorem _root_.solution {S S' : Scheme.{0}} (φ : S' ⟶ S) (X : Over S') (A : Over S) [GrpObj A]
    (a b : (Over.map φ).obj X ⟶ A) :
    (Over.mapPullbackAdj φ).homEquiv X A (a * b) =
      (Over.mapPullbackAdj φ).homEquiv X A a * (Over.mapPullbackAdj φ).homEquiv X A b := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]
end ReciprocityTheory.ChartRestriction.G.Out.UBC
