-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.rsm_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:03.723291+00:00
-- url     : https://prove2.me/submissions/a4bd3e92-2a6b-442f-867e-90e76ef56b54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Metric Set
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (N : ℕ) : Module.finrank ℝ (EuclideanSpace ℂ (Fin N)) = 2 * N := by
  first
    | rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]
    | rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
    | rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin N)), Complex.finrank_real_complex,
        finrank_euclideanSpace, Fintype.card_fin]
    | simp [finrank_real_of_complex]
end ReciprocityTheory.ChartRestriction.G.I2
