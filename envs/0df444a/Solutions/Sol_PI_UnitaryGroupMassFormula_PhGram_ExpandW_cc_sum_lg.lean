-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.ExpandW.cc_sum_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:31.735199+00:00
-- url     : https://prove2.me/submissions/b906d817-cac2-472d-ad35-87dd15c0bf55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Expand
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_cc_lg
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_cc_lg


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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhGram PI.UnitaryGroupMassFormula.PhGram.ExpandW
open PI.FglGram PI.UnitaryGroupMassFormula.PhGram
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]} {σ : Type}
namespace PI.UnitaryGroupMassFormula.PhGram.ExpandW
theorem _root_.solution (hd : Data l ex ph) {m : ℕ} {a : Fin m → MvPowerSeries σ ℂ_[p]}
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) :
    MvPowerSeries.constantCoeff (∑ j, lg l (a j)) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => cc_lg hd (ha j)
end PI.UnitaryGroupMassFormula.PhGram.ExpandW
