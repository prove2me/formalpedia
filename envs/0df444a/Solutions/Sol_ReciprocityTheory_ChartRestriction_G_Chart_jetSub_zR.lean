-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.jetSub_zR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:59.282422+00:00
-- url     : https://prove2.me/submissions/9a9d2b87-1fa9-497c-9002-055e5d755922

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftCompJetSub
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
theorem _root_.solution {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) (k : Fin b) :
    jetSub T m (zR m k) = ∑ i, T (Pi.single i 1) k • zR m i := by
  rw [jetSub, jetLift_zR]
end ReciprocityTheory.ChartRestriction.G.Chart
