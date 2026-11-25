-- Prove2me | solution 1 for PI.ScPiFrameW.hJ_self_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:30:59.806639+00:00
-- url     : https://prove2.me/submissions/6b58c0ed-af89-44ef-9794-d2e19649e2b6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
import Theorems.Thm_PI_ScPiFrameW_hJ_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScPiFrameW
open PI.ScPiExists
variable {n : ℕ}
namespace PI.ScPiFrameW
theorem _root_.solution (ε : Fin n → Bool) (x : Fin n → ℂ) :
    (hJ ε x x).re = ∑ j, (if ε j then (1 : ℝ) else -1) * Complex.normSq (x j) := by
  rw [hJ_self]; exact Complex.ofReal_re _
end PI.ScPiFrameW
