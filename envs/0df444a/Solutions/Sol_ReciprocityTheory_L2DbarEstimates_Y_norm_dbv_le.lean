-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.norm_dbv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:30:40.638924+00:00
-- url     : https://prove2.me/submissions/a80537ea-7b46-4ed0-aaec-fb671b704ad1

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} (D : V n →L[ℝ] ℂ) (ζ : V n) : ‖dbv D ζ‖ ≤ ‖D‖ * ‖ζ‖ := by
  have hI : ‖D (I • ζ)‖ ≤ ‖D‖ * ‖ζ‖ := by
    calc ‖D (I • ζ)‖ ≤ ‖D‖ * ‖I • ζ‖ := D.le_opNorm _
      _ = ‖D‖ * ‖ζ‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  have h1 : ‖D ζ + I * D (I • ζ)‖ ≤ ‖D‖ * ‖ζ‖ + ‖D‖ * ‖ζ‖ := by
    calc ‖D ζ + I * D (I • ζ)‖ ≤ ‖D ζ‖ + ‖I * D (I • ζ)‖ := norm_add_le _ _
      _ = ‖D ζ‖ + ‖D (I • ζ)‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ ‖D‖ * ‖ζ‖ + ‖D‖ * ‖ζ‖ := add_le_add (D.le_opNorm ζ) hI
  unfold dbv
  rw [norm_div, Complex.norm_two]
  linarith
end ReciprocityTheory.L2DbarEstimates.Y
