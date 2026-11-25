-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_zpow_sum__eeea0ab3dee3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:01:21.112889+00:00
-- url     : https://prove2.me/submissions/3f4d67e4-deed-488e-88d1-6dc8da1d3df3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_Transfer

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf
theorem _root_.solution {M : Type} [CommGroup M] {K : Type} (a : M) (s : Finset K) (f : K → ℤ) :
    a ^ (∑ k ∈ s, f k) = ∏ k ∈ s, a ^ f k := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons k s hk ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add, ih]
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
