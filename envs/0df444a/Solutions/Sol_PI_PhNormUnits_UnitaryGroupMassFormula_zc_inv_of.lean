-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.zc_inv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:09:55.307454+00:00
-- url     : https://prove2.me/submissions/323f47e2-69e8-4ee1-b933-3578c5125a35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_SimeqSubst1
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_zc_mul
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_zc_one
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_norm_zc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
variable {p : ℕ} [Fact p.Prime]
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (n : ℤ_[p]) (h : ‖zc n‖ = 1) : ∃ m : ℤ_[p], zc n * zc m = 1 := by
  rw [norm_zc] at h
  obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.mpr h
  refine ⟨((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), ?_⟩
  rw [← zc_mul, ← hu, Units.mul_inv, zc_one]
end PI.PhNormUnits.UnitaryGroupMassFormula
