-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_toLp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:34.812654+00:00
-- url     : https://prove2.me/submissions/778fab6f-8f42-40a3-bcda-313e055bb67e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradFPfA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.RGF
open Filter Topology Set ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RGF
theorem _root_.solution (n d : ℕ) (J : V n →L[ℂ] V d) (ξ : Fin n → ℂ) (b : Fin d) :
    J (WithLp.toLp 2 ξ) b = ∑ j, ξ j * J (bas n j) b := by
  have h : WithLp.toLp 2 ξ = ∑ j, ξ j • bas n j := by
    ext k
    simp [bas, Pi.single_apply]
  rw [h, map_sum]
  simp [map_smul]
end ReciprocityTheory.ChartRestriction.G.AR.Up.RGF
