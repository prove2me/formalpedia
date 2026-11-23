-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.rD_zR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:02.295967+00:00
-- url     : https://prove2.me/submissions/ce8e69a5-1960-4134-8ed0-945747431f0b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR


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
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (l : R × R →ₗ[R] R) (i : Fin 2) :
    rD l (zR 1 i) = TrivSqZeroExt.inr (l (if i = 0 then ((1 : R), (0 : R)) else (0, 1))) := by
  rw [rD, AlgHom.comp_apply, deltaJ, jetLift_zR, TrivSqZeroExt.map_inr]
end ReciprocityTheory.ChartRestriction.G.Chart
