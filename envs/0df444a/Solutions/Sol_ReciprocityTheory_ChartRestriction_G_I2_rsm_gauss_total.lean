-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.rsm_gauss_total
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:44.722933+00:00
-- url     : https://prove2.me/submissions/6f96ceb9-1c07-4ab9-9a33-dae1c2ff80bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rsm_finrank

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
theorem _root_.solution (N : ℕ) :
    ∫ z : EuclideanSpace ℂ (Fin N), Real.exp (-‖z‖ ^ 2) = Real.pi ^ N := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℂ (Fin N)) one_pos
  simp only [neg_mul, one_mul, div_one] at h
  first | rw [h] | erw [h]
  rw [rsm_finrank, show ((↑(2 * N) : ℝ) / 2) = ((N : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
end ReciprocityTheory.ChartRestriction.G.I2
