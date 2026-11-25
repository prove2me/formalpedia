-- Prove2me | solution 1 for PI.FockOneDegW.Core.SS_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:01.970891+00:00
-- url     : https://prove2.me/submissions/a4e845bf-a596-42ad-9aa2-2c141c5aef97

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Theorems.Thm_PI_FockOneDegW_Core_key
import Theorems.Thm_PI_FockOneDegW_Core_side_lp
import Theorems.Thm_PI_FockOneDegW_Core_side_sb
import Theorems.Thm_PI_FockOneDegW_Core_negOp_apply
import Theorems.Thm_PI_FockOneDegW_Core_posOp_apply
import Theorems.Thm_FockRaiseLowInner_fockInner_sum_left
import Theorems.Thm_FockRaiseLowInner_fockInner_sum_right
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
theorem _root_.solution (v : Pol p q r s) (a b : Ix p q) (hab : sameBlock a b) :
    SS v a b = fockInner (negOp b a v) (posOp a b v) := by
  have hs : a.isLeft = b.isLeft := (side_sb a b).1 hab
  rw [negOp_apply, posOp_apply, fockInner_sum_left]
  unfold SS
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [fockInner_sum_right]
  refine Finset.sum_congr rfl fun d _ => ?_
  unfold gg
  by_cases hD : linePos ((a, d) : Ln p q r s) = true
  · have hD' : linePos ((b, d) : Ln p q r s) = true := by
      rw [side_lp] at hD ⊢; rw [← hs]; exact hD
    by_cases hcd : sameBlock c d
    · have hbc : linePos ((b, c) : Ln p q r s) = true := by
        rw [side_lp, ← hs, (side_lp a d).1 hD]
        exact ((side_sb c d).1 hcd).symm
      rw [if_neg (fun h => h.1 hcd), if_pos hbc, fockInner_zero_left, fockInner_zero_left]
    · have hbc : ¬ linePos ((b, c) : Ln p q r s) = true := by
        intro h
        apply hcd
        rw [side_sb, ← (side_lp b c).1 h, ← hs]
        exact (side_lp a d).1 hD
      rw [if_pos ⟨hcd, hD⟩, if_pos ⟨hcd, hD'⟩, if_neg hbc, if_pos hD]
      apply key
      intro h
      apply hcd
      have : c = d := (Prod.mk.inj h).2
      subst this
      exact (side_sb c c).2 rfl
  · rw [if_neg (fun h => hD h.2), if_neg hD, fockInner_zero_left, fockInner_zero_right]
end PI.FockOneDegW.Core
