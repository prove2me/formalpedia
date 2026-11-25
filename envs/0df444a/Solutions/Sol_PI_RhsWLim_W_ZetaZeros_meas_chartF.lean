-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.meas_chartF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:36:48.959845+00:00
-- url     : https://prove2.me/submissions/81a899e3-6dba-457c-8d01-03c90ed5e56f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_meas_secP
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_meas_invM
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_cont_gC

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
open PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.ZetaZeros
theorem _root_.solution (hs : IsSection k r z z' μsec) : Measurable (chartF k r z z' μsec) := by
  have h := (cont_gC (k := k) (r := r)).measurable.comp (((meas_secP hs).comp measurable_fst).prodMk
    ((measurable_fst.comp measurable_snd).prodMk (meas_invM.comp (measurable_snd.comp measurable_snd))))
  exact h
end PI.RhsWLim.W.ZetaZeros
