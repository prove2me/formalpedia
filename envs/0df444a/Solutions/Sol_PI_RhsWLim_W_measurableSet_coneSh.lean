-- Prove2me | solution 1 for PI.RhsWLim.W.measurableSet_coneSh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:21.104948+00:00
-- url     : https://prove2.me/submissions/2188bc71-6bcd-4a93-8e46-cb4ac6d12619

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushV
import Theorems.Thm_PI_RhsWLim_W_continuous_qf
import Theorems.Thm_PI_RhsWLim_W_continuous_tau
import Theorems.Thm_PI_RhsWLim_W_coneSh_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution {T' : ℝ} (hT' : 0 < T') {E : Set ((Fin k → ℂ) × ℂ)} (hE : MeasurableSet E) :
    MeasurableSet (coneSh k T' E) := by
  rw [coneSh_eq hT']
  have hq := (continuous_qf (k := k)).measurable
  have htau := (continuous_tau (k := k) T').measurable
  simp only [Set.ofPred_and]
  refine (measurableSet_lt hq measurable_const).inter ((measurableSet_lt measurable_const htau).inter
    ((measurableSet_lt htau measurable_const).inter ?_))
  exact (htau.inv.smul measurable_id) hE
end PI.RhsWLim.W
