-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.wvol_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:14:22.103997+00:00
-- url     : https://prove2.me/submissions/01e2f289-9e9d-4e03-be66-8a3ae1d01f25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar

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
theorem _root_.solution (hT : 0 ≤ Tz k r z * Tz k r z') (n : ℕ) :
    (volume : Measure ℂ).withDensity (wD k r z z') (Metric.closedBall 0 n) < ⊤ := by
  rw [withDensity_apply _ measurableSet_closedBall]
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_closedBall
    (g := fun _ => ENNReal.ofReal (((n : ℝ) ^ 2) ^ (k - 1))) ?_) ?_
  · intro ζ hζ
    unfold wD
    split_ifs with h
    · apply ENNReal.ofReal_le_ofReal
      unfold zWeight
      rw [if_pos h.le]
      have h1 : Complex.normSq ζ ≤ (n : ℝ) ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.1 hζ) 2
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    · simp
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
end PI.RhsWLim.W.ZetaZeros
