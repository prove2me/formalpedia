-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:28.551793+00:00
-- url     : https://prove2.me/submissions/7ac3542f-c7e1-4bf5-bf22-a3bee12531cb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_meas_wD
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_meas_chartF
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_secP_eq
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_wD_zero_off
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_circle_ae

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
theorem _root_.solution (hD : WbData k r z z' μW μW' a a' μsec) (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ) :
    rhsW k r z z' μW μW' μsec φ = ∫⁻ x, φ x ∂nuR k r z z' μW μW' μsec := by
  have := hD.haarW.1
  have := hD.haarW'.1
  have hF := meas_chartF hD.sec
  have hΦ : Measurable (fun q => φ (chartF k r z z' μsec q)) := hφ.comp hF
  rw [nuR, lintegral_map hφ hF, srcM, lintegral_prod _ hΦ.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ meas_wD hΦ.lintegral_prod_right']
  unfold rhsW
  apply lintegral_congr_ae
  filter_upwards [circle_ae (Tz k r z * Tz k r z')] with ζ hζ
  simp only [Pi.mul_apply]
  rw [lintegral_prod (fun y : Mt k r × Mt k r => φ (chartF k r z z' μsec (ζ, y)))
    (hΦ.comp measurable_prodMk_left).aemeasurable]
  by_cases h : Tz k r z * Tz k r z' < Complex.normSq ζ
  · have hw : wD k r z z' ζ = ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) := by
      unfold wD
      exact if_pos h
    rw [hw]
    congr 1
    refine lintegral_congr fun x => lintegral_congr fun y => ?_
    have hc : chartF k r z z' μsec (ζ, x, y) =
        fun i j => (Matrix.of x * embWb k r (μsec ζ) * (Matrix.of y)⁻¹) i j := by
      unfold chartF
      rw [secP_eq h]
    exact congrArg φ hc.symm
  · have hlt : Complex.normSq ζ < Tz k r z * Tz k r z' := lt_of_le_of_ne (not_lt.1 h) hζ
    have hz : zWeight k (Tz k r z) (Tz k r z') ζ = 0 := by
      unfold zWeight
      exact if_neg (not_le.2 hlt)
    rw [wD_zero_off h, hz, ENNReal.ofReal_zero, zero_mul, zero_mul]
end PI.RhsWLim.W.ZetaZeros
