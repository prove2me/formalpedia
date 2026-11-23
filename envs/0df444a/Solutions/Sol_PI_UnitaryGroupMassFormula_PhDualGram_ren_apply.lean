-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhDualGram.ren_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:55.78668+00:00
-- url     : https://prove2.me/submissions/80852350-1c46-4275-965c-2d121c510dac

import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen

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
theorem _root_.solution (F : MvPowerSeries σ ℂ_[p]) :
    ren r F = MvPowerSeries.subst (fun s => (X (r s) : MvPowerSeries τ ℂ_[p])) F :=
  substAlgHom_apply _ F
end PI.UnitaryGroupMassFormula.PhDualGram
