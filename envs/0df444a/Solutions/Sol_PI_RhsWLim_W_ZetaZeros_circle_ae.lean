-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.circle_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:35:56.059045+00:00
-- url     : https://prove2.me/submissions/64da5037-c931-4e8c-b75f-36d4cd077111

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
theorem _root_.solution (c : ℝ) : ∀ᵐ ζ : ℂ ∂volume, Complex.normSq ζ ≠ c := by
  rw [ae_iff]
  refine measure_mono_null (fun ζ hζ => ?_) (Measure.addHaar_sphere (volume : Measure ℂ) (0 : ℂ) (Real.sqrt c))
  simp only [Set.mem_ofPred_eq, not_not] at hζ
  rw [mem_sphere_zero_iff_norm, ← hζ, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
end PI.RhsWLim.W.ZetaZeros
