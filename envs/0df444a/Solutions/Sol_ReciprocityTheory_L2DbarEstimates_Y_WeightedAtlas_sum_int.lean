-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.sum_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:01:59.187385+00:00
-- url     : https://prove2.me/submissions/708ffca1-5fab-4553-b8fc-d88c5c873f50

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_SetLIntegralBiUnionLe
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_continuous_nsq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_nsq_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_nsq_sum_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (A : WeightedAtlas n Y ι La) {la : La} {κ : Type*} (F : Finset κ)
    (h : κ → ι → Y → ℂ) (hh : ∀ q ∈ F, A.IsSec la (h q)) (Wt : Y → ℝ) (hWt : Measurable Wt)
    (hW0 : ∀ y, 0 ≤ Wt y)
    (hint : ∀ q ∈ F, ∫⁻ y, ENNReal.ofReal (A.nsq la (h q) y * Wt y) ∂A.mu < ⊤) :
    ∫⁻ y, ENNReal.ofReal (A.nsq la (fun i y => ∑ q ∈ F, h q i y) y * Wt y) ∂A.mu < ⊤ := by
  have hpt : ∀ y, ENNReal.ofReal (A.nsq la (fun i y => ∑ q ∈ F, h q i y) y * Wt y) ≤
      ENNReal.ofReal (F.card : ℝ) * ∑ q ∈ F, ENNReal.ofReal (A.nsq la (h q) y * Wt y) := by
    intro y
    rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => mul_nonneg (A.nsq_nonneg _ _ _) (hW0 y)),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← Finset.sum_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (A.nsq_sum_le la F h y) (hW0 y)
  calc _ ≤ ∫⁻ y, ENNReal.ofReal (F.card : ℝ) *
        ∑ q ∈ F, ENNReal.ofReal (A.nsq la (h q) y * Wt y) ∂A.mu := lintegral_mono hpt
    _ = ENNReal.ofReal (F.card : ℝ) * ∑ q ∈ F, ∫⁻ y, ENNReal.ofReal (A.nsq la (h q) y * Wt y) ∂A.mu := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum']
        intro q hq
        exact (ENNReal.measurable_ofReal.comp
          ((A.continuous_nsq (hh q hq)).measurable.mul hWt)).aemeasurable
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 hint)
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
