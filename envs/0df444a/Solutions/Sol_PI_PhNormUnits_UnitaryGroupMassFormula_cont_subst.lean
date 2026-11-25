-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.cont_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:32.544567+00:00
-- url     : https://prove2.me/submissions/8a9d0bbc-fb55-4f85-aeec-b98b09c4b03b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_coeff_subst_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical Filter Topology MvPowerSeries.WithPiTopology
open PI PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
variable {p : ℕ} [Fact p.Prime]
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution {τ : Type*} (G : ℂ_[p] → MvPowerSeries τ ℂ_[p])
    (hG : Continuous G) (h0 : ∀ x, MvPowerSeries.constantCoeff (G x) = 0) (f : PowerSeries ℂ_[p]) :
    Continuous fun x => (PowerSeries.subst (G x) f : MvPowerSeries τ ℂ_[p]) := by
  refine continuous_pi fun e => ?_
  change Continuous fun x => MvPowerSeries.coeff e (PowerSeries.subst (G x) f : MvPowerSeries τ ℂ_[p])
  simp_rw [coeff_subst_sum _ (h0 _), smul_eq_mul]
  refine continuous_finsetSum _ fun d _ => continuous_const.mul ?_
  exact (continuous_coeff ℂ_[p] e).comp (hG.pow d)
end PI.PhNormUnits.UnitaryGroupMassFormula
