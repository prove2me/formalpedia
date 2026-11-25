-- Prove2me | solution 1 for PI.QuotInvW.weil_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:26:38.477663+00:00
-- url     : https://prove2.me/submissions/c2305dd7-9fed-467a-b5c2-75c536e1cafa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
import Theorems.Thm_PI_QuotInvW_measurable_mm_left
import Theorems.Thm_PI_QuotInvW_ae_mem_S
import Theorems.Thm_PI_QuotInvW_weil
import Theorems.Thm_PI_QuotInvW_ae_mem_G

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open PI PI.QuotInvW
variable {m : ℕ}
variable {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
namespace PI.QuotInvW
theorem _root_.solution (h : QuotientSetting G S μG μS ν) {H f : MtM m → ℝ≥0∞} (hH : Measurable H)
    (hf : Measurable f) (hHi : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → H (mm s x) = H x) :
    ∫⁻ x, H x * f x ∂μG = ∫⁻ x, H x * (∫⁻ s, f (mm s x) ∂μS) ∂ν := by
  have hW := weil h (hH.mul hf)
  simp only [Pi.mul_apply] at hW
  rw [hW]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_G h] with x hx
  rw [← lintegral_const_mul (H x) (f := fun s => f (mm s x)) (hf.comp (measurable_mm_left x))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_S h] with s hs
  rw [show H (mm s x) = H x from hHi _ hs x hx]
end PI.QuotInvW
