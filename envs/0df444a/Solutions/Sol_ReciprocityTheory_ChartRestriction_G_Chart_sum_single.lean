-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.sum_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:59.235914+00:00
-- url     : https://prove2.me/submissions/153330c0-6481-40c8-9b3e-160ae669d78d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftCompJetSub

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
theorem _root_.solution {a : ℕ} (c : Fin a → R) : ∑ i, c i • Pi.single i (1 : R) = c := by
  ext k
  simp [Pi.single_apply]
end ReciprocityTheory.ChartRestriction.G.Chart
