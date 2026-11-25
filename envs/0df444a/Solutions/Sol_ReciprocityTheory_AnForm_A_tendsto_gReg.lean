-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.tendsto_gReg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:36.931505+00:00
-- url     : https://prove2.me/submissions/4f2ad247-d165-41c5-b6ae-74c356c6c79a

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
theorem _root_.solution {ζ : ℂ} (hζ : ζ ≠ 0) :
    Tendsto (fun k : ℕ => gReg (1 / ((k : ℝ) + 1)) ζ) atTop (𝓝 (Real.log ‖ζ‖)) := by
  have hr2 : 0 < ‖ζ‖ ^ 2 := by have := norm_pos_iff.2 hζ; positivity
  have h1 : Tendsto (fun k : ℕ => ‖ζ‖ ^ 2 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (‖ζ‖ ^ 2 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at h1
  have h2 := ((Real.continuousAt_log hr2.ne').tendsto.comp h1).const_mul (1 / 2 : ℝ)
  have h3 : (1 / 2 : ℝ) * Real.log (‖ζ‖ ^ 2) = Real.log ‖ζ‖ := by
    rw [Real.log_pow]; push_cast; ring
  rw [h3] at h2
  exact h2
end ReciprocityTheory.AnForm.A
