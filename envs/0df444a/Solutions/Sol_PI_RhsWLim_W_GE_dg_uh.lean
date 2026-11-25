-- Prove2me | solution 1 for PI.RhsWLim.W.GE.dg_uh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:23:54.666157+00:00
-- url     : https://prove2.me/submissions/600035f6-5f23-4b3e-9712-f9e33dceea53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ChartLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_GaugeExists
import Theorems.Thm_PI_RhsWLim_W_GE_splitHermForm_firstMiddle_apply
import Theorems.Thm_PI_RhsWLim_W_GE_splitHermForm_apply_firstMiddle

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
theorem _root_.solution (u : ℂ) (hu : star u * u = 1) : dg k r u ∈ UH (Hpk k r) := by
  show (dg k r u)ᴴ * Hpk k r * dg k r u = Hpk k r
  unfold dg
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul]
  by_cases hi : i = p0 k r <;> by_cases hj : j = p0 k r
  · subst hi
    subst hj
    simp only [Pi.star_apply, if_true]
    linear_combination (Hpk k r (p0 k r) (p0 k r)) * hu
  · subst hi
    simp only [Pi.star_apply, if_true, if_neg hj, splitHermForm_firstMiddle_apply j hj, mul_zero, zero_mul]
  · subst hj
    simp only [Pi.star_apply, if_true, if_neg hi, splitHermForm_apply_firstMiddle i hi, mul_zero, zero_mul]
  · simp only [Pi.star_apply, if_neg hi, if_neg hj, star_one, one_mul, mul_one]
end PI.RhsWLim.W.GE
