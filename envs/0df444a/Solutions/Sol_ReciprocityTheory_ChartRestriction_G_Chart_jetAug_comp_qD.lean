-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.jetAug_comp_qD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:29.151332+00:00
-- url     : https://prove2.me/submissions/340d863a-c65e-4207-a987-470851ed9dd7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_qD_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR


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
theorem _root_.solution (i : Fin 2) : (jetAug R (Fin 2) 1).comp (qD i) = fstD R := by
  ext a
  rw [AlgHom.comp_apply, qD_apply, map_add, map_smul, AlgHom.commutes, jetAug_zR, smul_zero, add_zero]
  rfl
end ReciprocityTheory.ChartRestriction.G.Chart
