-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_comp_base_eq__bbdd29943377
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:59:10.771416+00:00
-- url     : https://prove2.me/submissions/b5039622-d526-49ec-a0bd-54bb3ec62c0c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_WchartInlLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ActActA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_CompBaseEq

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
theorem _root_.solution {A B C : Scheme.{0}} {a b : A ⟶ B} {ψ : B ⟶ C} (h : a ≫ ψ = b ≫ ψ) (z : A) :
    ψ (a z) = ψ (b z) := by
  rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
