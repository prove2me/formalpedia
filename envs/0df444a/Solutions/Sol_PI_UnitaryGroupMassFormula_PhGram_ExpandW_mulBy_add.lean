-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.ExpandW.mulBy_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:26.389177+00:00
-- url     : https://prove2.me/submissions/793502cb-dce1-4661-856f-188180f8cf47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Expand
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_cc_lg
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_lg_pt
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_cc_lg
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
theorem _root_.solution (hd : Data l ex ph) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (e e' : ℂ_[p]) : mulBy l ex (e + e') a = add l ex (mulBy l ex e a) (mulBy l ex e' a) := by
  unfold mulBy add
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.C e * lg l a) = 0 := by
    rw [map_mul, cc_lg hd ha, mul_zero]
  have h2 : MvPowerSeries.constantCoeff (MvPowerSeries.C e' * lg l a) = 0 := by
    rw [map_mul, cc_lg hd ha, mul_zero]
  rw [lg_pt hd h1, lg_pt hd h2, map_add, add_mul]
end PI.UnitaryGroupMassFormula.PhGram.ExpandW
