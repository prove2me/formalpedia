-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.snd_rD_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:47.397794+00:00
-- url     : https://prove2.me/submissions/c41ab80e-7d23-42fd-a3b8-03360b658314

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst

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
theorem _root_.solution (a : JetR R (Fin 2) 1) :
    (rD (LinearMap.fst R R R + LinearMap.snd R R R) a).snd =
      (rD (LinearMap.fst R R R) a).snd + (rD (LinearMap.snd R R R) a).snd := by
  simp only [rD, AlgHom.comp_apply, TrivSqZeroExt.snd_map, LinearMap.add_apply]
end ReciprocityTheory.ChartRestriction.G.Chart
