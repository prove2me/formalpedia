-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.ExpandW.add_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:27.83684+00:00
-- url     : https://prove2.me/submissions/3c299969-693b-488a-9576-9404e1008016

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Expand
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_lg_pt
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_lg_pt


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
theorem _root_.solution (hd : Data l ex ph) {x : MvPowerSeries σ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (b : MvPowerSeries σ ℂ_[p]) : add l ex (pt ex x) b = pt ex (x + lg l b) := by
  unfold add
  rw [lg_pt hd hx]
end PI.UnitaryGroupMassFormula.PhGram.ExpandW
