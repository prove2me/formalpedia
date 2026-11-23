-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_PhGram_integral_subst__38f52d75ab58
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:09.674111+00:00
-- url     : https://prove2.me/submissions/f8dcd5ec-fad5-4caf-83c9-1ddf9753ca22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsSubstitution
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_PAdicPowerSeriesCoefficients_integral_subst


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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhGram
open PI.FglGram
variable {p : ℕ} [Fact p.Prime]
open PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients
namespace PI.UnitaryGroupMassFormula.PhGram
theorem _root_.solution {σ τ : Type*} [Finite τ] (s : τ → MvPowerSeries σ ℂ_[p]) (hs : ∀ i, Good (s i))
    {f : MvPowerSeries τ ℂ_[p]} (hf : IntegralMv f) : IntegralMv (MvPowerSeries.subst s f) := by
  exact integral_subst s (fun i => (hs i).1) (fun i => (hs i).2) hf
end PI.UnitaryGroupMassFormula.PhGram
