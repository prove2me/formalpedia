-- Prove2me | solution 1 for PI.FglPhSplit.Wk.deg_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:24.803827+00:00
-- url     : https://prove2.me/submissions/a24f5bab-e1d1-4f95-ac1a-69d8721c5019

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit MvPowerSeries Finset
variable {K : Type} [Field K] {σ : Type}
namespace PI.FglPhSplit.Wk
theorem _root_.solution (α : σ →₀ ℕ) : (α.sum fun _ k => k) = Finsupp.degree α := by rfl
end PI.FglPhSplit.Wk
