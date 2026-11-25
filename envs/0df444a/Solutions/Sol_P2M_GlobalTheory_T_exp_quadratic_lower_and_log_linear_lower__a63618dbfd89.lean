-- Prove2me | solution 1 for P2M_GlobalTheory_T_exp_quadratic_lower_and_log_linear_lower__a63618dbfd89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:28.492799+00:00
-- url     : https://prove2.me/submissions/42c8fa19-b1c2-4fed-8c78-13fa36116b7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpQuadraticLowerAndLogLinearLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpQuadraticLowerAndLogLinearLowerStatement
import Theorems.Thm_GlobalTheory_exp_quadratic_lower_and_log_linear_lower


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : (∀ u : ℝ, |u| ≤ 1 → 1 + u + u ^ 2 / 3 ≤ Real.exp u) ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 3 → 3 * u / 4 ≤ Real.log (1 + u) := by
  first | exact @GlobalTheory.exp_quadratic_lower_and_log_linear_lower | exact GlobalTheory.exp_quadratic_lower_and_log_linear_lower | (intros; apply GlobalTheory.exp_quadratic_lower_and_log_linear_lower <;> assumption)
end _root_.GlobalTheory.T
