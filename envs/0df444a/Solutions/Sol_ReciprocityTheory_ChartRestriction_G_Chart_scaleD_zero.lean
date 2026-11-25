-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.scaleD_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:46:48.882536+00:00
-- url     : https://prove2.me/submissions/cf12b8ca-4c30-48f5-bd80-1394b296579e

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
theorem _root_.solution : scaleD (0 : R) = (Algebra.ofId R (DualNumber R)).comp (fstD R) := by
  apply DualNumber.algHom_ext
  show TrivSqZeroExt.map _ (TrivSqZeroExt.inr 1) = (Algebra.ofId R (DualNumber R)) ((TrivSqZeroExt.inr (1 : R) : DualNumber R).fst)
  rw [TrivSqZeroExt.map_inr, zero_smul, LinearMap.zero_apply, TrivSqZeroExt.fst_inr, map_zero, TrivSqZeroExt.inr_zero]
end ReciprocityTheory.ChartRestriction.G.Chart
