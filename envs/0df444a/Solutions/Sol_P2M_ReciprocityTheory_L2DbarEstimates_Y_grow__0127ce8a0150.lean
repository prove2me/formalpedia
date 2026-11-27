-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_Y_grow__0127ce8a0150
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:14:28.885337+00:00
-- url     : https://prove2.me/submissions/4a9e0cd8-3560-436a-a71f-026719e3e03c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GrowSumIndicatorLe

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
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
namespace grow
theorem _root_.solution.{u1, u2} (hC : GROWCountStatement.{u1, u2}) : GROWStatement.{u1, u2} := by
  intro X _ μ Γ _ _ _ _ _ _ D B F ps x' C Sup m hD hB hF hps hinv hm hmv hSup
  set φ : X → ℝ≥0∞ := fun x => ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-ps x)) with hφdef
  have hφ : Measurable φ :=
    ENNReal.measurable_ofReal.comp
      (((hF.norm).pow_const 2).mul (Real.measurable_exp.comp hps.neg))
  have hcount := hC X μ Γ D B φ m hD hB hφ (fun γ x => by simp only [hφdef, hinv]) hm
  have hB2 : ∫⁻ x in B, ENNReal.ofReal (‖F x‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (Real.exp Sup) * ∫⁻ x in B, φ x ∂μ := by
    rw [← lintegral_const_mul _ hφ]
    refine setLIntegral_mono ((hφ.const_mul _)) fun x hx => ?_
    rw [hφdef]
    dsimp only
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have h1 : 1 ≤ Real.exp Sup * Real.exp (-ps x) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith [hSup x hx])
    have h2 : 0 ≤ ‖F x‖ ^ 2 := by positivity
    nlinarith
  calc ENNReal.ofReal (‖F x'‖ ^ 2) ≤ C * ∫⁻ x in B, ENNReal.ofReal (‖F x‖ ^ 2) ∂μ := hmv
    _ ≤ C * (ENNReal.ofReal (Real.exp Sup) * (m * ∫⁻ x in D, φ x ∂μ)) := by
        gcongr
        exact hB2.trans (by gcongr)
    _ = C * m * ENNReal.ofReal (Real.exp Sup) * ∫⁻ x in D, φ x ∂μ := by ring
end grow
end ReciprocityTheory.L2DbarEstimates.Y
