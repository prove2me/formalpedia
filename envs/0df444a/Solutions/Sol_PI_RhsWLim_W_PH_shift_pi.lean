-- Prove2me | solution 1 for PI.RhsWLim.W.PH.shift_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:42.601229+00:00
-- url     : https://prove2.me/submissions/b8364635-1583-461d-b278-2ebc6750b162

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PolarHyp

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
open MeasureTheory Filter Topology Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.PH
namespace PI.RhsWLim.W.PH
theorem _root_.solution (K : ℝ → ℝ≥0∞) :
    ∫⁻ φ in Ioo (-Real.pi) Real.pi, K (φ + Real.pi) = ∫⁻ θ in Ioc 0 (2 * Real.pi), K θ := by
  rw [← lintegral_indicator measurableSet_Ioo,
    ← setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)),
    ← lintegral_indicator measurableSet_Ioo,
    ← lintegral_add_right_eq_self (fun θ => (Ioo 0 (2 * Real.pi)).indicator K θ) Real.pi]
  congr 1
  funext φ
  by_cases h : φ ∈ Ioo (-Real.pi) Real.pi
  · have h' : φ + Real.pi ∈ Ioo 0 (2 * Real.pi) := ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [indicator_of_mem h, indicator_of_mem h']
  · have h' : φ + Real.pi ∉ Ioo 0 (2 * Real.pi) := fun h' => h ⟨by linarith [h'.1], by linarith [h'.2]⟩
    rw [indicator_of_notMem h, indicator_of_notMem h']
end PI.RhsWLim.W.PH
