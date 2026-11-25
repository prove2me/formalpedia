-- Prove2me | solution 1 for PI.FockOneDegW.RedOps.inner_negOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:20.395509+00:00
-- url     : https://prove2.me/submissions/a17b19ef-1c43-40b0-b920-7b33c0f3af24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockRaiseLow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps
import Theorems.Thm_FockRL_linePos_left
import Theorems.Thm_FockRL_sameBlock_symm
import Theorems.Thm_FockRaiseLowInner_fockInner_X_mul
import Theorems.Thm_FockRaiseLowInner_fockInner_mul_X
import Theorems.Thm_FockRaiseLowInner_fockInner_sum_left
import Theorems.Thm_FockRaiseLowInner_fockInner_sum_right
import Theorems.Thm_FockRaiseLowInner_fockInner_zero_left
import Theorems.Thm_FockRaiseLowInner_fockInner_zero_right
import Theorems.Thm_PI_FockOneDegW_negOp_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
open PI PI.FockOneDegW PI.FockOneDegW.RedOps
open PI.FockOneDegW
variable {p q r s : ℕ}
namespace PI.FockOneDegW.RedOps
theorem _root_.solution (a b : Ix p q) (hab : sameBlock a b) (P Q : Pol p q r s) :
    fockInner P (negOp a b Q) = fockInner (negOp b a P) Q := by
  rw [negOp_apply, negOp_apply, fockInner_sum_right, fockInner_sum_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hl : linePos ((b, c) : Ln p q r s) = linePos ((a, c) : Ln p q r s) :=
    (FockRL.linePos_left b a c).2 (FockRL.sameBlock_symm hab)
  rw [hl]
  split_ifs
  · rw [fockInner_zero_right, fockInner_zero_left]
  · rw [fockInner_mul_X, fockInner_X_mul]
end PI.FockOneDegW.RedOps
