-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.nu_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:42:12.373299+00:00
-- url     : https://prove2.me/submissions/6bad145a-891d-463d-8b06-0dcc65e55836

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_meas_chartF

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
theorem _root_.solution (hD : WbData k r z z' μW μW' a a' μsec) : nuR k r z z' μW μW' μsec ≠ 0 := by
  have := hD.haarW.1
  have := hD.haarW'.1
  intro h0
  have h1 : nuR k r z z' μW μW' μsec Set.univ = 0 := by rw [h0]; rfl
  rw [nuR, Measure.map_apply (meas_chartF hD.sec) MeasurableSet.univ, Set.preimage_univ, srcM,
    ← Set.univ_prod_univ, Measure.prod_prod, ← Set.univ_prod_univ, Measure.prod_prod, hD.massW, hD.massW'] at h1
  rcases mul_eq_zero.1 h1 with h | h
  · have hc : 0 ≤ Tz k r z * Tz k r z' := (mul_pos hD.T_pos hD.T'_pos).le
    have hEo : IsOpen {ζ : ℂ | Tz k r z * Tz k r z' + 1 < Complex.normSq ζ} :=
      isOpen_lt continuous_const Complex.continuous_normSq
    have hEn : ({ζ : ℂ | Tz k r z * Tz k r z' + 1 < Complex.normSq ζ}).Nonempty := by
      refine ⟨((Tz k r z * Tz k r z' + 2 : ℝ) : ℂ), ?_⟩
      show Tz k r z * Tz k r z' + 1 < Complex.normSq _
      rw [Complex.normSq_ofReal]
      nlinarith
    have hE := hEo.measure_pos (volume : Measure ℂ) hEn
    have hle : volume {ζ : ℂ | Tz k r z * Tz k r z' + 1 < Complex.normSq ζ} ≤
        (volume : Measure ℂ).withDensity (wD k r z z') {ζ : ℂ | Tz k r z * Tz k r z' + 1 < Complex.normSq ζ} := by
      rw [withDensity_apply _ hEo.measurableSet, ← setLIntegral_one]
      refine setLIntegral_mono' hEo.measurableSet fun ζ hζ => ?_
      have hζ' : Tz k r z * Tz k r z' + 1 < Complex.normSq ζ := hζ
      have hD' : Tz k r z * Tz k r z' < Complex.normSq ζ := by linarith
      unfold wD zWeight
      rw [if_pos hD', if_pos hD'.le, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith))
    exact (ne_of_gt (lt_of_lt_of_le hE (hle.trans (measure_mono (Set.subset_univ _))))) h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd (ENNReal.ofReal_eq_zero.1 h) (not_le.2 hD.a_pos)
    · exact absurd (ENNReal.ofReal_eq_zero.1 h) (not_le.2 hD.a'_pos)
end PI.RhsWLim.W.ZetaZeros
