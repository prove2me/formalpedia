-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.isTan_dualLift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:50.292949+00:00
-- url     : https://prove2.me/submissions/392a8051-ee79-4568-902d-565d8e3f889a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_IsUnivChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_jetAug_alt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
include hx
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (c : Fin n → R) : IsTan (spMap (dualLift c) ≫ x 1) := by
  rw [IsTan, ← Category.assoc, spMap_comp, fstD_comp_dualLift]
  exact spMap_jetAug_alt hx 1
end ReciprocityTheory.ChartRestriction.G.Chart
