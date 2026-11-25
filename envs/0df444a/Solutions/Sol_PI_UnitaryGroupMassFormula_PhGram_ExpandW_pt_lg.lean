-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.ExpandW.pt_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:15.761511+00:00
-- url     : https://prove2.me/submissions/b90f416b-d87d-41fa-a35c-0e7882c211a3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Expand
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_cc_l
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_ex_l
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_cc_l


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
theorem _root_.solution (hd : Data l ex ph) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    pt ex (lg l a) = a := by
  unfold pt lg
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero (cc_l hd))
    (PowerSeries.HasSubst.of_constantCoeff_zero ha), ex_l hd,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
end PI.UnitaryGroupMassFormula.PhGram.ExpandW
