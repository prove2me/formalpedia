-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhDualGram.ren_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:04.308317+00:00
-- url     : https://prove2.me/submissions/e6173b3c-b9ef-4f26-b6b4-024a871450e9

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
theorem _root_.solution (s : σ) : ren r (X s : MvPowerSeries σ ℂ_[p]) = X (r s) := by
  rw [ren_apply, MvPowerSeries.subst_X (hasSubst_ren r)]
end PI.UnitaryGroupMassFormula.PhDualGram
