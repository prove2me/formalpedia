-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.meas_secP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:36:05.910423+00:00
-- url     : https://prove2.me/submissions/eb15316a-8bb7-4180-88c0-30b8fa57a869

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
theorem _root_.solution (hs : IsSection k r z z' μsec) :
    Measurable (fun ζ : ℂ => (fun i j => secP k r z z' μsec ζ i j : Fin (k + 1) → Fin (k + 1) → ℂ)) := by
  have e : (fun ζ : ℂ => (fun i j => secP k r z z' μsec ζ i j : Fin (k + 1) → Fin (k + 1) → ℂ)) =
      {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ}.piecewise
        (fun ζ => (fun i j => μsec ζ i j : Fin (k + 1) → Fin (k + 1) → ℂ))
        (fun _ => (fun i j => (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j)) := by
    funext ζ
    by_cases h : Tz k r z * Tz k r z' < Complex.normSq ζ <;> simp [secP, Set.piecewise, h]
  rw [e]
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const
    (isOpen_lt continuous_const Complex.continuous_normSq).measurableSet
  exact continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hs.1 i j).continuousOn
end PI.RhsWLim.W.ZetaZeros
