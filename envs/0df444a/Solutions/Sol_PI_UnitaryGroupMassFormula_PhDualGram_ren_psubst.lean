-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhDualGram.ren_psubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:04.06006+00:00
-- url     : https://prove2.me/submissions/3c90f628-d871-447d-bd8f-4a9e741c6600

import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_apply

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhDualGram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime]
variable {σ τ : Type} [Finite σ] (r : σ → τ)
namespace PI.UnitaryGroupMassFormula.PhDualGram
theorem _root_.solution (P : PowerSeries ℂ_[p]) {y : MvPowerSeries σ ℂ_[p]} (hy : constantCoeff y = 0) :
    ren r (PowerSeries.subst y P) = PowerSeries.subst (ren r y) P := by
  rw [ren_apply, ren_apply, PowerSeries.subst, PowerSeries.subst]
  exact MvPowerSeries.subst_comp_subst_apply
    (PowerSeries.hasSubst_iff.mp (PowerSeries.HasSubst.of_constantCoeff_zero hy)) (hasSubst_ren r) P
end PI.UnitaryGroupMassFormula.PhDualGram
