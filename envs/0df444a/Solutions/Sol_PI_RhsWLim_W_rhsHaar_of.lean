-- Prove2me | solution 1 for PI.RhsWLim.W.rhsHaar_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:19:17.455223+00:00
-- url     : https://prove2.me/submissions/374b3f9e-667e-42cf-b1b6-8d865806a9d7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_meas_chartF
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_mem_chart
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_src_null
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_repr
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_nu_sigmaFinite
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_nu_ne_zero
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_nu_inv
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_nu_ball
import Theorems.Thm_PI_RhsWLim_W_HU_amb_closed


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
open ZetaZeros
namespace PI.RhsWLim.W
theorem _root_.solution (hInv : RhsWInv) : RhsHaar := by
  intro k r z z' μW μW' a a' μsec hD
  have := hD.haarW.1
  have := hD.haarW'.1
  refine ⟨nuR k r z z' μW μW' μsec, ⟨nu_sigmaFinite hD, nu_ne_zero hD, ?_, fun s hs => nu_inv hInv hD s hs⟩,
    nu_ball hD, fun φ hφ => repr hD φ hφ⟩
  rw [nuR, Measure.map_apply (meas_chartF hD.sec) (s := {x : Mt k r | Matrix.of x ∉ UWb k r})
    HU.amb_closed.isOpen_compl.measurableSet]
  exact measure_mono_null (fun q hq hg => hq (mem_chart hD hg)) (src_null hD)
end PI.RhsWLim.W
