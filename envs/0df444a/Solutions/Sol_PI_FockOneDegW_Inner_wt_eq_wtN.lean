-- Prove2me | solution 1 for PI.FockOneDegW.Inner.wt_eq_wtN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:08.029395+00:00
-- url     : https://prove2.me/submissions/b57d3485-eacb-4723-8d82-52e044eb78ae

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action FockRaiseLowInner
open PI PI.FockOneDegW PI.FockOneDegW.Inner
variable {σ : Type*}
namespace PI.FockOneDegW.Inner
theorem _root_.solution (α : σ →₀ ℕ) : wt α = (wtN α : ℂ) := by
  simp only [wt, wtN, Finsupp.prod, Nat.cast_prod]
end PI.FockOneDegW.Inner
