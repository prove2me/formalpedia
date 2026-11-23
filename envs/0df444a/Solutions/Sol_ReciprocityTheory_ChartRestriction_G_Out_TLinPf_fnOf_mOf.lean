-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.fnOf_mOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:15.260745+00:00
-- url     : https://prove2.me/submissions/491e64b6-ba91-4daa-9d3b-9a3a71edee2a

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
theorem _root_.solution {X : Scheme.{0}} (ρ : Γ(X, ⊤)) : fnOf (mOf ρ) = ρ := by
  have h : (mOf ρ).appTop = (Scheme.ΓSpecIso _).hom ≫
      CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) ρ) := by
    rw [mOf, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
  rw [fnOf, h, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  simp
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
