-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.ExpandW.be_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:41.825409+00:00
-- url     : https://prove2.me/submissions/f410afd4-0784-4053-88a8-19bc3ccee102

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Expand
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_pt_lg
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_lg_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_phAt_zero
import Theorems.Thm_PI_FglPhSplit_Wk_pt_lg


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
theorem _root_.solution (hd : Data l ex ph) {b : MvPowerSeries σ ℂ_[p]} (hb : MvPowerSeries.constantCoeff b = 0) :
    be l ex ph 0 b = 0 := by
  unfold be add
  rw [lg_zero hd, zero_add, pt_lg hd hb, phAt_zero hd]
  ring
end PI.UnitaryGroupMassFormula.PhGram.ExpandW
