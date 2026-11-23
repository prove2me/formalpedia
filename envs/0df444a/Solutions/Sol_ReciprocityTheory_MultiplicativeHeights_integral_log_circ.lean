-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.integral_log_circ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:23.116949+00:00
-- url     : https://prove2.me/submissions/a12f741f-166f-44ec-bc46-1d8df0c20383

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_circPt_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Polynomial Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (p : ℂ[X]) :
    ∫ t in Set.Ioc (0 : ℝ) 1, Real.log ‖p.eval (circPt t)‖ = p.logMahlerMeasure := by
  rw [← intervalIntegral.integral_of_le zero_le_one, logMahlerMeasure_def, circleAverage_def]
  simp only [circPt_eq]
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.log ‖p.eval (circleMap 0 1 x)‖)
    (by positivity : (2 * π) ≠ 0)]
  simp
end ReciprocityTheory.MultiplicativeHeights
