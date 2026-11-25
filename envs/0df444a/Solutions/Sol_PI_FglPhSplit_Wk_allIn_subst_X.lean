-- Prove2me | solution 1 for PI.FglPhSplit.Wk.allIn_subst_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:46:37.253188+00:00
-- url     : https://prove2.me/submissions/4505b701-29df-40cd-a665-74eab99485a9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Theorems.Thm_PI_FglPhSplit_Wk_allIn_mul
import Theorems.Thm_PI_FglPhSplit_Wk_allIn_one
import Theorems.Thm_PI_FglPhSplit_Wk_allIn_X
import Theorems.Thm_PI_FglPhSplit_Wk_allIn_pow

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
open PI.FglPhSplit
variable {K : Type} [Field K]
namespace PI.FglPhSplit.Wk
theorem _root_.solution {W : Subring K} {σ τ : Type} (r : σ → τ)
    (ha : MvPowerSeries.HasSubst (fun s => (MvPowerSeries.X (r s) : MvPowerSeries τ K)))
    {H : MvPowerSeries σ K} (hH : AllIn W H) :
    AllIn W (MvPowerSeries.subst (fun s => (MvPowerSeries.X (r s) : MvPowerSeries τ K)) H) := by
  classical
  intro e
  rw [MvPowerSeries.coeff_subst ha]
  refine finsum_induction (p := fun x => x ∈ W) W.zero_mem (fun _ _ => W.add_mem) fun d => ?_
  rw [smul_eq_mul]
  refine W.mul_mem (hH d) ?_
  have : AllIn W (∏ s ∈ d.support, (MvPowerSeries.X (r s) : MvPowerSeries τ K) ^ (d s)) :=
    Finset.prod_induction _ (AllIn W) (fun _ _ => allIn_mul) allIn_one
      fun s _ => allIn_pow (allIn_X _) _
  exact this e
end PI.FglPhSplit.Wk
