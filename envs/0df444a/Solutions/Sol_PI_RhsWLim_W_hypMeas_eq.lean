-- Prove2me | solution 1 for PI.RhsWLim.W.hypMeas_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:37:20.880455+00:00
-- url     : https://prove2.me/submissions/85986aa1-e1b5-4da7-b42d-5bf0946bf7f7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Theorems.Thm_PI_RhsWLim_W_continuous_hypPar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (k : ℕ) (T' : ℝ) {f : (Fin k → ℂ) × ℂ → ℝ≥0∞} (hf : Measurable f) :
    hypMeas k T' f = ∫⁻ p, f p ∂hypM k T' := by
  have hm : Measurable (hypPar k T') := (continuous_hypPar k T').measurable
  unfold hypM hypMeas
  rw [lintegral_smul_measure, smul_eq_mul, lintegral_map hf hm,
    lintegral_prod (fun a => f (hypPar k T' a)) (hf.comp hm).aemeasurable]
  rfl
end PI.RhsWLim.W
