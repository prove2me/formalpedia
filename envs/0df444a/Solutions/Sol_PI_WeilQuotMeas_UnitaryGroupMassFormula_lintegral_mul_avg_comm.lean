-- Prove2me | solution 1 for PI.WeilQuotMeas.UnitaryGroupMassFormula.lintegral_mul_avg_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:12:09.355399+00:00
-- url     : https://prove2.me/submissions/66e2734b-4b92-43e6-9926-480d6facb76a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeilQuotMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_StepBruhat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_LintegralMulAvgComm
import Theorems.Thm_PI_WeilQuotMeas_UnitaryGroupMassFormula_measurable_mul_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal Pointwise
open PI PI.WeilQuotMeas PI.WeilQuotMeas.UnitaryGroupMassFormula
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
namespace PI.WeilQuotMeas.UnitaryGroupMassFormula
theorem _root_.solution (μ : Measure G) (ν : Measure H) [SFinite μ] [SFinite ν]
    [μ.IsMulRightInvariant] [ν.IsInvInvariant] {f β : G → ℝ≥0∞} (hf : Measurable f)
    (hβ : Measurable β) :
    ∫⁻ g, f g * ∫⁻ h, β (g * (h : G)) ∂ν ∂μ = ∫⁻ g, β g * ∫⁻ h, f (g * (h : G)) ∂ν ∂μ := by
  calc ∫⁻ g, f g * ∫⁻ h, β (g * (h : G)) ∂ν ∂μ
      = ∫⁻ g, ∫⁻ h, f g * β (g * (h : G)) ∂ν ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_const_mul]
        exact hβ.comp (measurable_const.mul measurable_subtype_coe)
    _ = ∫⁻ h, ∫⁻ g, f g * β (g * (h : G)) ∂μ ∂ν :=
        lintegral_lintegral_swap ((hf.comp measurable_fst).mul (hβ.comp measurable_mul_coe)).aemeasurable
    _ = ∫⁻ h, ∫⁻ g, f (g * ((h : G))⁻¹) * β g ∂μ ∂ν := by
        refine lintegral_congr fun h => ?_
        have e := lintegral_mul_right_eq_self (μ := μ) (fun x => f (x * ((h : G))⁻¹) * β x) (h : G)
        simp only [mul_inv_cancel_right] at e
        exact e
    _ = ∫⁻ g, ∫⁻ h, f (g * ((h : G))⁻¹) * β g ∂ν ∂μ :=
        lintegral_lintegral_swap ((hf.comp (measurable_snd.mul
          (measurable_subtype_coe.comp measurable_fst).inv)).mul (hβ.comp measurable_snd)).aemeasurable
    _ = ∫⁻ g, β g * ∫⁻ h, f (g * (h : G)) ∂ν ∂μ := by
        refine lintegral_congr fun g => ?_
        have e := lintegral_inv_eq_self (μ := ν) (fun h : H => f (g * (h : G)))
        simp only [InvMemClass.coe_inv] at e
        rw [lintegral_mul_const, e]
        · exact mul_comm _ _
        · exact hf.comp (measurable_const.mul measurable_subtype_coe.inv)
end PI.WeilQuotMeas.UnitaryGroupMassFormula
