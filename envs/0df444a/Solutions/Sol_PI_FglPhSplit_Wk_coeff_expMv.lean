-- Prove2me | solution 1 for PI.FglPhSplit.Wk.coeff_expMv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:24.203955+00:00
-- url     : https://prove2.me/submissions/eb767c55-c3f3-426d-a0a9-2d3ddd4b09b1

import Definitions.Def_Formalism_PeriodIntegrals_FglPhSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development

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
open PI.FglPhSplit MvPowerSeries
namespace PI.FglPhSplit.Wk
theorem _root_.solution {K : Type} [Field K] {σ : Type} (f : MvPowerSeries σ K) (α : σ →₀ ℕ) :
    coeff α (expMv f) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1), coeff α (f ^ n) / (n.factorial : K) := rfl
end PI.FglPhSplit.Wk
