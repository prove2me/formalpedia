-- Prove2me | solution 1 for PI.ScPiFrameW.hJ_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:53.540661+00:00
-- url     : https://prove2.me/submissions/ada9ed05-d878-44d9-9a1b-76c7b13258c1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
import Theorems.Thm_PI_ScPiFrameW_star_sg
import Theorems.Thm_PI_ScPiFrameW_hJ_eq_sum

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
theorem _root_.solution (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  rw [hJ_eq_sum, hJ_eq_sum, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_mul', star_mul', star_star, star_sg]; ring
end PI.ScPiFrameW
