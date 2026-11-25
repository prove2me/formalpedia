-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.abs_det_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:05:17.736096+00:00
-- url     : https://prove2.me/submissions/266e3a5a-e42e-40f2-8ec1-0d29d396586a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG

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
open MeasureTheory Set Filter Topology Function
variable {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (f : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
    |(f.restrictScalars ℝ).det| = ‖LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by
  have h : (f.restrictScalars ℝ).det =
      Complex.normSq (LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) := by
    show LinearMap.det ((f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)).restrictScalars ℝ) = _
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  rw [h, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
end ReciprocityTheory.ChartRestriction.G.Geo
