-- Prove2me | solution 1 for PI.RhsWLim.W.GE.exp_dV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:00.860742+00:00
-- url     : https://prove2.me/submissions/8c2abbe5-e49e-4444-9e51-5845139cd2d3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ChartLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_GaugeExists

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
open scoped ENNReal NNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
open PI.RhsWLim.W.GE
variable {k r : ℕ}
namespace PI.RhsWLim.W.GE
theorem _root_.solution (t : ℝ) : NormedSpace.exp ((t : ℂ) • diagonal (dV k r)) = dg k r (Complex.exp (t * Complex.I)) := by
  unfold dg
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext i
  simp only [Pi.smul_apply, dV, smul_eq_mul]
  split_ifs
  · rw [Complex.exp_eq_exp_ℂ]
  · rw [mul_zero, NormedSpace.exp_zero]
end PI.RhsWLim.W.GE
