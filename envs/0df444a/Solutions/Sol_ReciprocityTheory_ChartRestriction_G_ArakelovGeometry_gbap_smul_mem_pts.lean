-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_smul_mem_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:34.216642+00:00
-- url     : https://prove2.me/submissions/6296a422-aa08-402e-90fc-c920e2b2326c

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_eval_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_coordIdeal_isHomogIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {Ω : Type} [Field Ω] [CharZero Ω]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {J : Type} [Fintype J] (x : J → Ω) {z : J → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) {c : ℂ} (hc : c ≠ 0) : c • z ∈ pts (coordIdeal ℤ x) := by
  refine ⟨smul_ne_zero hc hz.1, fun f hf => ?_⟩
  have hH := coordIdeal_isHomogIdeal ℤ x
  rw [← sum_homogeneousComponent f, map_sum, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [gbap_eval_smul ((homogeneousComponent_isHomogeneous d f).map _),
    hz.2 _ (hH f hf d), mul_zero]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
