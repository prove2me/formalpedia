-- Prove2me | solution 1 for PI.FglPhSplit.Wk.coeff_expMv_eq_expT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:19.717004+00:00
-- url     : https://prove2.me/submissions/2610ce1b-4e4d-46c9-9588-418fbfb2b960

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Theorems.Thm_PI_FglPhSplit_Wk_deg_eq
import Theorems.Thm_P2M_PI_FglPhSplit_Wk_coeff_pow_eq_zero__60e911f4ed32
import Theorems.Thm_PI_FglPhSplit_Wk_coeff_expT

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
theorem _root_.solution {f : MvPowerSeries σ K} (hf : constantCoeff f = 0) {α : σ →₀ ℕ}
    {N : ℕ} (hN : Finsupp.degree α < N) : coeff α (expMv f) = coeff α (expT f N) := by
  rw [coeff_expT]
  change (∑ n ∈ range ((α.sum fun _ k => k) + 1), coeff α (f ^ n) / (n.factorial : K)) = _
  rw [deg_eq]
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_range] at hn ⊢
    omega
  · intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [coeff_pow_eq_zero' hf (by omega), zero_div]
end PI.FglPhSplit.Wk
