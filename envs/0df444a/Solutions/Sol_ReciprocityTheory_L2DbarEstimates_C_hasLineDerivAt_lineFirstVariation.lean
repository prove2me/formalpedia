-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.hasLineDerivAt_lineFirstVariation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:37:18.206702+00:00
-- url     : https://prove2.me/submissions/d16353f2-bf36-4e02-8d59-c6889d0de686

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_hasDerivAt_halfLogRatioSqDeriv
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_hasDerivAt_line
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_hasDerivAt_realLine_fderiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {z : V n} (hz : z ∈ Ω) {ε : ℝ} (hε : 0 < ε) (e : V n)
    (μ : ℂ) :
    HasLineDerivAt ℝ (fun w => lineFirstVariation ε (F w) (fderiv ℂ F w e * μ))
      (lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ)) z (μ • e) := by
  have hp := hasDerivAt_line hΩ hF hz e μ
  have hq := (hasDerivAt_realLine_fderiv hΩ hF hz e μ).mul_const μ
  have hs : HasDerivAt (fun t : ℝ => ‖F (z + t • (μ • e))‖ ^ 2)
      (2 * inner ℝ (F z) (fderiv ℂ F z e * μ)) 0 := by
    simpa using hp.norm_sq
  have h1' : HasDerivAt (halfLogRatioSqDeriv ε) (halfLogRatioSqSecondDeriv ε (‖F z‖ ^ 2))
      ((fun t : ℝ => ‖F (z + t • (μ • e))‖ ^ 2) 0) := by
    simpa using hasDerivAt_halfLogRatioSqDeriv (ε := ε) (s := ‖F z‖ ^ 2) (by positivity)
  have h1 := h1'.comp 0 hs
  have h2 := (hp.inner (𝕜 := ℝ) hq).const_mul 2
  show HasDerivAt (fun t : ℝ => halfLogRatioSqDeriv ε (‖F (z + t • (μ • e))‖ ^ 2) *
    (2 * inner ℝ (F (z + t • (μ • e))) (fderiv ℂ F (z + t • (μ • e)) e * μ))) _ 0
  refine (h1.mul h2).congr_deriv ?_
  simp only [zero_smul, add_zero, Function.comp_apply]
  unfold lineSecondVariation
  ring
end ReciprocityTheory.L2DbarEstimates.C
