-- Prove2me | solution 1 for PI.QuotInvW.avgS_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:28:06.45324+00:00
-- url     : https://prove2.me/submissions/7b4c9760-baf8-4401-bd48-f31183c46089

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableAvgS
import Theorems.Thm_PI_QuotInvW_measurable_mm_left


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
    (hpos : ∀ x, f x ≠ 0) (x : MtM m) : avgS μS f x ≠ 0 := by
  intro h0
  unfold avgS at h0
  have h1 := (lintegral_eq_zero_iff (f := fun s => f (mm s x)) (hf.comp (measurable_mm_left x))).1 h0
  have hμ : μS Set.univ = 0 := by
    have := ae_iff.1 h1
    simpa [hpos] using this
  exact h.2.2.2.2.1.2.1 (Measure.measure_univ_eq_zero.1 hμ)
end PI.QuotInvW
