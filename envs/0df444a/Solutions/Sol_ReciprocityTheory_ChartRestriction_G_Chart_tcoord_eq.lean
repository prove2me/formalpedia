-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tcoord_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:27:20.593184+00:00
-- url     : https://prove2.me/submissions/338ca089-7597-4653-96fc-09c08af5745a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_IsUnivChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec

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
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (w : sp (R₀ := R) (DualNumber R) ⟶ G) (hw : IsTan w) (c : Fin n → R)
    (hc : w = spMap (dualLift c) ≫ x 1) : tcoord hx w hw = c :=
  (exists_coord hx w hw).unique (tcoord_spec hx w hw) hc
end ReciprocityTheory.ChartRestriction.G.Chart
