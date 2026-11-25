-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.twb_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:18:03.412625+00:00
-- url     : https://prove2.me/submissions/04374924-c6a1-4728-a105-2e3113588cdc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwBound
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℂ) (ρ : α → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hρm : Measurable ρ) (hρ : ∀ x, 0 ≤ ρ x) :
    ∫⁻ x, ENNReal.ofReal (‖f x - g x‖ ^ 2 * ρ x) ∂μ ≤
      2 * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * ρ x) ∂μ +
        2 * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2 * ρ x) ∂μ := by
  have hm1 : Measurable (fun x => ENNReal.ofReal (‖f x‖ ^ 2 * ρ x)) :=
    ((hf.norm.pow_const 2).mul hρm).ennreal_ofReal
  have hm2 : Measurable (fun x => ENNReal.ofReal (‖g x‖ ^ 2 * ρ x)) :=
    ((hg.norm.pow_const 2).mul hρm).ennreal_ofReal
  calc ∫⁻ x, ENNReal.ofReal (‖f x - g x‖ ^ 2 * ρ x) ∂μ
      ≤ ∫⁻ x, (2 * ENNReal.ofReal (‖f x‖ ^ 2 * ρ x) + 2 * ENNReal.ofReal (‖g x‖ ^ 2 * ρ x)) ∂μ := by
        refine lintegral_mono (fun x => ?_)
        have ha : 0 ≤ ‖f x‖ ^ 2 * ρ x := mul_nonneg (sq_nonneg _) (hρ x)
        have hb : 0 ≤ ‖g x‖ ^ 2 * ρ x := mul_nonneg (sq_nonneg _) (hρ x)
        have h1 : ‖f x - g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_sub_le _ _
        have h3 : ‖f x - g x‖ ^ 2 ≤ (‖f x‖ + ‖g x‖) ^ 2 := by gcongr
        have h2 : ‖f x - g x‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖g x‖ ^ 2 := by
          nlinarith [sq_nonneg (‖f x‖ - ‖g x‖)]
        have key : ‖f x - g x‖ ^ 2 * ρ x ≤ 2 * (‖f x‖ ^ 2 * ρ x) + 2 * (‖g x‖ ^ 2 * ρ x) := by
          have h4 := mul_le_mul_of_nonneg_right h2 (hρ x)
          linarith
        calc ENNReal.ofReal (‖f x - g x‖ ^ 2 * ρ x)
            ≤ ENNReal.ofReal (2 * (‖f x‖ ^ 2 * ρ x) + 2 * (‖g x‖ ^ 2 * ρ x)) :=
              ENNReal.ofReal_le_ofReal key
          _ = 2 * ENNReal.ofReal (‖f x‖ ^ 2 * ρ x) + 2 * ENNReal.ofReal (‖g x‖ ^ 2 * ρ x) := by
              rw [ENNReal.ofReal_add (by positivity) (by positivity),
                ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
              simp
    _ = 2 * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * ρ x) ∂μ +
          2 * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2 * ρ x) ∂μ := by
        rw [lintegral_add_left (hm1.const_mul 2), lintegral_const_mul 2 hm1,
          lintegral_const_mul 2 hm2]
end ReciprocityTheory.L2DbarEstimates.I
