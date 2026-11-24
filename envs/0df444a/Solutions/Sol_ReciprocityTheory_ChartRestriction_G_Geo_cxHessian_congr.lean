-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.cxHessian_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:14.797686+00:00
-- url     : https://prove2.me/submissions/a605a60c-cbb2-4dd6-96f2-57f0298ec17c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial Filter Topology
variable {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {f g : (Fin e → ℂ) → ℝ} {y : Fin e → ℂ} (h : f =ᶠ[𝓝 y] g) :
    cxHessian f y = cxHessian g y := by
  have h2 : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := h.fderiv.fderiv_eq
  unfold cxHessian
  rw [h2]
end ReciprocityTheory.ChartRestriction.G.Geo
