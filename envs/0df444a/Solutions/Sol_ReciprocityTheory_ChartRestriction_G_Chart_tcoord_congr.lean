-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:52.515494+00:00
-- url     : https://prove2.me/submissions/cc9cccb8-2f33-4465-9a56-ab2339d83a36

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftCompJetSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR epsScaleR IsTangent IsLieComb IsLieBasis)
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {w w' : sp (R₀ := R) (DualNumber R) ⟶ G} (e : w = w') (h : IsTan w)
    (h' : IsTan w') : tcoord hx w h = tcoord hx w' h' := by
  subst e; rfl
end ReciprocityTheory.ChartRestriction.G.Chart
