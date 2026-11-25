-- Prove2me | solution 1 for PI.RhsWLim.W.lintegral_inv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:15:47.071999+00:00
-- url     : https://prove2.me/submissions/558d1efc-998e-404a-b0ed-1af5a5312514

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushM

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
variable {k : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution {t : ℝ} (ht : 0 < t) {G : (Fin k → ℂ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y, G (t⁻¹ • y) = ENNReal.ofReal (t ^ Module.finrank ℝ (Fin k → ℂ)) * ∫⁻ y, G y := by
  have hH : (volume : Measure (Fin k → ℂ)).IsAddHaarMeasure := inferInstance
  set f : (Fin k → ℂ) →ₗ[ℝ] (Fin k → ℂ) := t⁻¹ • LinearMap.id with hfdef
  have hdet : LinearMap.det f = (t⁻¹) ^ Module.finrank ℝ (Fin k → ℂ) := by
    rw [hfdef, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hdet0 : LinearMap.det f ≠ 0 := by rw [hdet]; exact pow_ne_zero _ (inv_ne_zero ht.ne')
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin k → ℂ))) hdet0
  rw [hdet, inv_pow, inv_inv, abs_of_pos (pow_pos ht _)] at hmap
  have hfm : Measurable f := f.continuous_of_finiteDimensional.measurable
  have e : (fun y : Fin k → ℂ => G (t⁻¹ • y)) = fun y => G (f y) := by
    funext y
    simp [hfdef]
  rw [e, ← lintegral_map hG hfm, hmap, lintegral_smul_measure, smul_eq_mul]
end PI.RhsWLim.W
