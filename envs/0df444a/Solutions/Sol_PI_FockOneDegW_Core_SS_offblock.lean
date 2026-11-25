-- Prove2me | solution 1 for PI.FockOneDegW.Core.SS_offblock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:07.742026+00:00
-- url     : https://prove2.me/submissions/60300c90-a682-4fcf-908d-ddd72fcab981

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Theorems.Thm_PI_FockOneDegW_Core_side_lp
import Theorems.Thm_PI_FockOneDegW_Core_side_sb
import Theorems.Thm_FockRaiseLowInner_fockInner_zero_left
import Theorems.Thm_FockRaiseLowInner_fockInner_zero_right


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
theorem _root_.solution (v : Pol p q r s) (a b : Ix p q) (h : ¬ sameBlock a b) : SS v a b = 0 := by
  refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
  unfold gg
  by_cases h1 : (¬ sameBlock c d) ∧ linePos ((a, d) : Ln p q r s) = true
  · by_cases h2 : (¬ sameBlock c d) ∧ linePos ((b, d) : Ln p q r s) = true
    · exfalso
      apply h
      rw [side_sb]
      rw [(side_lp a d).1 h1.2, (side_lp b d).1 h2.2]
    · rw [if_neg h2, fockInner_zero_right]
  · rw [if_neg h1, fockInner_zero_left]
end PI.FockOneDegW.Core
