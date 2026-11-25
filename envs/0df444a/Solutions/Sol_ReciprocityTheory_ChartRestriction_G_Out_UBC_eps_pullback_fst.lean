-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.UBC.eps_pullback_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:49:40.360452+00:00
-- url     : https://prove2.me/submissions/8b2bdc2a-0216-4991-9c60-dd462005b833

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
theorem _root_.solution {S S' : Scheme.{0}} (f : S' ⟶ S) :
    (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫ pullback.fst (𝟙_ (Over S)).hom f = f := by
  have h1 : (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫ pullback.snd (𝟙_ (Over S)).hom f =
      𝟙 S' :=
    Over.w (Functor.LaxMonoidal.ε (Over.pullback f))
  have h2 : pullback.fst (𝟙_ (Over S)).hom f = pullback.snd (𝟙_ (Over S)).hom f ≫ f :=
    (Category.comp_id _).symm.trans pullback.condition
  rw [h2, ← Category.assoc, h1]
  exact Category.id_comp f
end ReciprocityTheory.ChartRestriction.G.Out.UBC
