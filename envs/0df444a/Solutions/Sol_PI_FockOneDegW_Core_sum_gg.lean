-- Prove2me | solution 1 for PI.FockOneDegW.Core.sum_gg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:10.993927+00:00
-- url     : https://prove2.me/submissions/4de5217d-e924-4224-bc72-69510ecd3106

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag
variable {p q r s : ℕ}
namespace PI.FockOneDegW.Core
theorem _root_.solution (v : Pol p q r s)
    (hH : ∀ c d : Ix r s, ¬ sameBlock c d → lowOp (p := p) (q := q) c d v = 0) (c d : Ix r s) :
    ∑ a : Ix p q, gg v a c d = 0 := by
  by_cases h : sameBlock c d
  · exact Finset.sum_eq_zero fun a _ => by simp [gg, h]
  · rw [← hH c d h, lowOp, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hl : linePos ((a, d) : Ln p q r s) = true
    · simp [gg, h, hl]
    · simp [gg, h, hl]
end PI.FockOneDegW.Core
