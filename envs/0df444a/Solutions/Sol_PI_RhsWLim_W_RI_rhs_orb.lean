-- Prove2me | solution 1 for PI.RhsWLim.W.RI.rhs_orb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:13:30.596224+00:00
-- url     : https://prove2.me/submissions/6ac4c23e-226a-4c3c-9b9c-5c144502eaac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvO
import Theorems.Thm_PI_RhsWLim_W_RI_inv_fix


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
open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.RI
theorem _root_.solution (hd : WbData k r z z' μW μW' a a' μsec) (F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞) :
    rhsW k r z z' μW μW' μsec (fun x => F (orbV k r z' x)) = ENNReal.ofReal a' *
      ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * Gf μW F (embWb k r (μsec ζ) *ᵥ z') := by
  unfold rhsW
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ζ => ?_
  have inner : ∀ h : Mt k r, ∫⁻ h', F (orbV k r z'
      (fun i j => (Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j)) ∂μW' =
        ENNReal.ofReal a' * F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) := by
    intro h
    have hae : ∀ᵐ h' ∂μW', Matrix.of h' ∈ UWset k r z' := by
      rw [ae_iff]
      exact hd.haarW'.2.2.1
    calc ∫⁻ h', F (orbV k r z' (fun i j => (Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j)) ∂μW'
        = ∫⁻ h', F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) ∂μW' := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with h' hh'
          show F ((Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) *ᵥ z') =
            F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z'))
          rw [← Matrix.mulVec_mulVec, inv_fix (HU.isUnit_of_uh hh'.1) hh'.2.2, ← Matrix.mulVec_mulVec]
      _ = F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) * μW' Set.univ := lintegral_const _
      _ = ENNReal.ofReal a' * F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) := by rw [hd.massW', mul_comm]
  simp_rw [inner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold Gf
  ring
end PI.RhsWLim.W.RI
