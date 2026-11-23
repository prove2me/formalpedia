-- Prove2me | solution 1 for PI.FglPhSplit.Wk.coeff_expT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:24.464823+00:00
-- url     : https://prove2.me/submissions/6094295a-6137-415f-b06c-f84a104f4950

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
theorem _root_.solution (f : MvPowerSeries σ K) (N : ℕ) (α : σ →₀ ℕ) :
    coeff α (expT f N) = ∑ n ∈ range N, coeff α (f ^ n) / (n.factorial : K) := by
  simp only [expT, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_eq_inv_mul]
end PI.FglPhSplit.Wk
