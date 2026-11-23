-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.integrableOn_log_circ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:23.014154+00:00
-- url     : https://prove2.me/submissions/9d6d6c2b-bdfb-4ee0-a073-159f83461321

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
    IntegrableOn (fun t => Real.log ‖p.eval (circPt t)‖) (Set.Ioc (0 : ℝ) 1) := by
  have h := (p.intervalIntegrable_mahlerMeasure).comp_mul_left (c := 2 * π) enorm_ne_top
    enorm_ne_top
  have h2 : IntervalIntegrable (fun t => Real.log ‖p.eval (circPt t)‖) volume 0 1 := by
    simp only [circPt_eq]
    convert h using 2 <;> simp
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h2
end ReciprocityTheory.MultiplicativeHeights
