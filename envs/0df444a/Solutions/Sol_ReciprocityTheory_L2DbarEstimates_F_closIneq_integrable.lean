-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.closIneq_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:13:42.810495+00:00
-- url     : https://prove2.me/submissions/cb526b21-3420-4ad2-ad87-043540b77dab

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Closure
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_closIneq_lint_ip_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
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
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [MeasurableSpace M] {n : ℕ} (μ : Measure M) (φ : M → ℝ)
    (hφ : Measurable φ) (v h : M → V n) (hv : AEStronglyMeasurable v μ)
    (hh : AEStronglyMeasurable h μ)
    (hv2 : ∫⁻ x, ENNReal.ofReal (‖v x‖ ^ 2 * Real.exp (-φ x)) ∂μ < ⊤)
    (hh2 : ∫⁻ x, ENNReal.ofReal (‖h x‖ ^ 2 * Real.exp (-φ x)) ∂μ < ⊤) :
    Integrable (fun x => ⟪v x, h x⟫_ℂ * (Real.exp (-φ x) : ℂ)) μ := by
  refine ⟨(hv.inner hh).mul (Complex.measurable_ofReal.comp hφ.neg.exp).aestronglyMeasurable, ?_⟩
  have h1 := closIneq_lint_ip_le μ φ hφ v h hv hh
  have hlt := lt_of_le_of_lt h1 (ENNReal.mul_lt_top hv2 hh2)
  show ∫⁻ x, ‖⟪v x, h x⟫_ℂ * (Real.exp (-φ x) : ℂ)‖ₑ ∂μ < ⊤
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc] at hlt
  simp at hlt
end ReciprocityTheory.L2DbarEstimates.F
