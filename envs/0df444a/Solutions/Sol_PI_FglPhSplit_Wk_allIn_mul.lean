-- Prove2me | solution 1 for PI.FglPhSplit.Wk.allIn_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:07.285817+00:00
-- url     : https://prove2.me/submissions/a3e5a975-7e43-4f2b-bd0a-6739bbfbe876

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum

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
theorem _root_.solution {W : Subring K} {σ : Type} {F G : MvPowerSeries σ K} (hF : AllIn W F)
    (hG : AllIn W G) : AllIn W (F * G) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hF _) (hG _)
end PI.FglPhSplit.Wk
