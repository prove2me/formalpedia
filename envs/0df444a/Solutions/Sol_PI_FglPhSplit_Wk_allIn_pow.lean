-- Prove2me | solution 1 for PI.FglPhSplit.Wk.allIn_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:16.766141+00:00
-- url     : https://prove2.me/submissions/a4779c40-2938-4d18-8149-24bbe89da0c1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Theorems.Thm_PI_FglPhSplit_Wk_allIn_mul
import Theorems.Thm_PI_FglPhSplit_Wk_allIn_one

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
theorem _root_.solution {W : Subring K} {σ : Type} {F : MvPowerSeries σ K} (hF : AllIn W F) (n : ℕ) :
    AllIn W (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact allIn_one
  | succ n ih => rw [pow_succ]; exact allIn_mul ih hF
end PI.FglPhSplit.Wk
