-- Prove2me | solution 1 for PI.QuotInvW.avgS_mm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:27:59.892545+00:00
-- url     : https://prove2.me/submissions/8a6d4741-b9a4-4426-bc64-b479661975c1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableAvgS
import Theorems.Thm_PI_QuotInvW_measurable_mm_left
import Theorems.Thm_PI_QuotInvW_mm_assoc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal NNReal
noncomputable section
open PI PI.QuotInvW
variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
namespace PI.QuotInvW
theorem _root_.solution (h : QuotientSetting G S μG μS ν) {f : MtM m → ℝ≥0∞} (hf : Measurable f)
    {t : MtM m} (ht : Matrix.of t ∈ S) (y : MtM m) : avgS μS f (mm t y) = avgS μS f y := by
  have hR : μS.map (rmulQ (Matrix.of t)) = μS := h.2.2.2.2.2.2.1 _ ht
  have hg : Measurable fun s => f (mm s y) := hf.comp (measurable_mm_left y)
  unfold avgS
  symm
  calc ∫⁻ s, f (mm s y) ∂μS = ∫⁻ s, f (mm s y) ∂(μS.map (rmulQ (Matrix.of t))) := by rw [hR]
    _ = ∫⁻ s, f (mm (rmulQ (Matrix.of t) s) y) ∂μS := lintegral_map hg (measurable_mm_left t)
    _ = ∫⁻ s, f (mm s (mm t y)) ∂μS := by
        congr 1; funext s
        rw [← mm_assoc]; rfl
end PI.QuotInvW
