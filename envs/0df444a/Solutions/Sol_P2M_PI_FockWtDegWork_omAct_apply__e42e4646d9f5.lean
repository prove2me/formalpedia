-- Prove2me | solution 1 for P2M_PI_FockWtDegWork_omAct_apply__e42e4646d9f5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:58.623795+00:00
-- url     : https://prove2.me/submissions/98340026-77fa-4816-ab74-c203f714bcfd

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockWtDegWork
namespace PI.FockWtDegWork
theorem _root_.solution (p q r s : ℕ) (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s M = ∑ l, ∑ l', M l l' • omE l l' := by
  unfold FockH1Action.omAct
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [LinearMap.sum_apply] <;> rfl
end PI.FockWtDegWork
