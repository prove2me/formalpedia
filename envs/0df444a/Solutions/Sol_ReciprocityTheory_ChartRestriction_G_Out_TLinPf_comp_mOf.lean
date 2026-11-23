-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.comp_mOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:15.141122+00:00
-- url     : https://prove2.me/submissions/ee772dc1-ab23-42f8-a7de-9065f43d3e6f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp

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
theorem _root_.solution {X Y : Scheme.{0}} (y : Y ⟶ X) (ρ : Γ(X, ⊤)) :
    y ≫ mOf ρ = mOf (y.appTop.hom ρ) := by
  rw [mOf, mOf, ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  congr 2
  ext1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp
  · simp
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
