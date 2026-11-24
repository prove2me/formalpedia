-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.gReg_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:31.681808+00:00
-- url     : https://prove2.me/submissions/fa71bc45-e1aa-479a-9442-9b813084d6c0

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {ζ : ℂ} (hζ : ζ ≠ 0) :
    |gReg ε ζ| ≤ |Real.log ‖ζ‖| + (1 / 2) * Real.log (‖ζ‖ ^ 2 + 1) := by
  have hr : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
  have hr2 : 0 < ‖ζ‖ ^ 2 := by positivity
  have hl1 : 0 ≤ Real.log (‖ζ‖ ^ 2 + 1) := Real.log_nonneg (by linarith)
  have hup : Real.log (‖ζ‖ ^ 2 + ε) ≤ Real.log (‖ζ‖ ^ 2 + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlo : Real.log (‖ζ‖ ^ 2) ≤ Real.log (‖ζ‖ ^ 2 + ε) := Real.log_le_log hr2 (by linarith)
  have h2 : Real.log (‖ζ‖ ^ 2) = 2 * Real.log ‖ζ‖ := by rw [Real.log_pow]; push_cast; ring
  unfold gReg
  rcases le_or_gt 0 (Real.log (‖ζ‖ ^ 2 + ε)) with h | h
  · rw [abs_of_nonneg (by linarith)]
    have := abs_nonneg (Real.log ‖ζ‖)
    linarith
  · rw [abs_of_neg (by linarith)]
    have := neg_abs_le (Real.log ‖ζ‖)
    linarith
end ReciprocityTheory.AnForm.A
