-- Prove2me | solution 1 for PI.QuotInvW.measurable_avgS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:21:54.525985+00:00
-- url     : https://prove2.me/submissions/20a0a8a7-09b8-459e-a5e7-9065e203f15c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableAvgS
import Theorems.Thm_PI_QuotInvW_measurable_mm


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
theorem _root_.solution [SFinite μS] {f : MtM m → ℝ≥0∞} (hf : Measurable f) :
    Measurable (avgS μS f) := by
  exact (hf.comp (measurable_mm (m := m))).lintegral_prod_left'
end PI.QuotInvW
