-- Prove2me | solution 1 for PI.RhsWLim.W.circle_null
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:15:41.111321+00:00
-- url     : https://prove2.me/submissions/b2dbd708-b79b-44ad-bba6-eb6328d115e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest

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
theorem _root_.solution (c : ℝ) : (volume : Measure ℂ) {ζ | Complex.normSq ζ = c} = 0 := by
  have hsub : {ζ : ℂ | Complex.normSq ζ = c} ⊆ Metric.sphere (0 : ℂ) (Real.sqrt c) := by
    intro ζ hζ
    have hζ' : Complex.normSq ζ = c := hζ
    rw [mem_sphere_zero_iff_norm, ← hζ', Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg ζ)]
  exact measure_mono_null hsub (Measure.addHaar_sphere volume 0 _)
end PI.RhsWLim.W
