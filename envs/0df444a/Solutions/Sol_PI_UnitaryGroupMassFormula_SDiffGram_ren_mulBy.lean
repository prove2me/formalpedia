-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.SDiffGram.ren_mulBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:30.333573+00:00
-- url     : https://prove2.me/submissions/002417db-e121-47aa-abad-470b5c1e29dc

import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_BeMulByZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramDifferenceRenaming_RenGramRhs
import Theorems.Thm_PI_UnitaryGroupMassFormula_SDiffGram_cc_lg
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_expMv_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_sub
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_int_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_simeq_iff_good
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_cc_lin
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_C
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_PhOn
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_X
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_be
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_lin
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_psubst
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_simeq_ren


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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SDiffGram
open PI.FglGram MvPowerSeries
open PI.UnitaryGroupMassFormula.PhDualGram (ren ren_apply ren_psubst ren_X ren_C simeq_ren cc_lin ren_lin ren_be ren_PhOn)
open PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram (Good simeq_iff_good good_add good_sub expMv_zero int_one)
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}
namespace PI.UnitaryGroupMassFormula.SDiffGram
theorem _root_.solution (hl0 : PowerSeries.constantCoeff l = 0) {σ τ : Type} [Finite σ] (r : σ → τ)
    (c : ℂ_[p]) {x : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0) :
    ren (p := p) r (mulBy l ex c x) = mulBy l ex c (ren r x) := by
  have h : constantCoeff (C c * lg l x) = 0 := by rw [map_mul, cc_lg hl0 hx, mul_zero]
  have e1 : mulBy l ex c x = PowerSeries.subst (C c * lg l x) ex := rfl
  have e2 : lg l x = PowerSeries.subst x l := rfl
  have e3 : mulBy l ex c (ren r x) = PowerSeries.subst (C c * PowerSeries.subst (ren r x) l) ex := rfl
  rw [e1, ren_psubst r _ h, map_mul, ren_C, e2, ren_psubst r _ hx, e3]
end PI.UnitaryGroupMassFormula.SDiffGram
