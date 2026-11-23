-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.const_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:44.981676+00:00
-- url     : https://prove2.me/submissions/114a87d0-f02f-483e-a5f6-70935584d0a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_isAb_pullback

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
theorem _root_.solution (hGF : GlobalFnsSt) {S S' : Scheme.{0}} (φ : S' ⟶ S) (A : Over S)
    [GrpObj A] (hA : IsAbelianScheme A) (v : Γ(((Over.pullback φ).obj A).left, ⊤)) :
    ∃ κ : Γ(S', ⊤), ((Over.pullback φ).obj A).hom.appTop.hom κ = v :=
  (hGF _ _ (isAb_pullback φ A hA)).2 v
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
