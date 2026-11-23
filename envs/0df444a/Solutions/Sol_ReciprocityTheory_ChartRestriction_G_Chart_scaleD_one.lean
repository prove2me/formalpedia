-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.scaleD_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:11.584272+00:00
-- url     : https://prove2.me/submissions/b0e56275-71b5-4beb-915f-687195ae9816

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
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution : scaleD (1 : R) = AlgHom.id R (DualNumber R) := by
  apply DualNumber.algHom_ext
  show TrivSqZeroExt.map _ (TrivSqZeroExt.inr 1) = TrivSqZeroExt.inr 1
  rw [TrivSqZeroExt.map_inr, one_smul, LinearMap.id_apply]
end ReciprocityTheory.ChartRestriction.G.Chart
