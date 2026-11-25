-- Prove2me | solution 1 for PI.RhsWLim.W.PH.lintegral_polar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:36.929347+00:00
-- url     : https://prove2.me/submissions/e0a7d515-ef7d-42a4-b95d-c354f152a9ec

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
theorem _root_.solution (Ψ : ℂ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ ζ, Ψ ζ = ∫⁻ R in Ioi (0 : ℝ), ENNReal.ofReal R *
      ∫⁻ φ in Ioo (-Real.pi) Real.pi, Ψ (R * (Real.cos φ + Real.sin φ * Complex.I)) := by
  have hm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * Ψ (p.1 * (Real.cos p.2 + Real.sin p.2 * Complex.I)) := by
    fun_prop
  rw [← Complex.lintegral_comp_polarCoord_symm,
    show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi from rfl, Measure.volume_eq_prod,
    ← Measure.prod_restrict]
  simp only [Complex.polarCoord_symm_apply, smul_eq_mul]
  rw [lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun R => ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
end PI.RhsWLim.W.PH
