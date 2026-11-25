-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.tmLog_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:20:22.1978+00:00
-- url     : https://prove2.me/submissions/93222894-c9b8-4202-9dbc-03ff633e9b22

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_norm_eval_torus_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    tmLog f θ ≤ posLog (∑ s ∈ f.support, ‖f.coeff s‖) := by
  unfold tmLog
  rcases eq_or_ne ‖MvPolynomial.eval (torusPoint θ) f‖ 0 with h | h
  · rw [h, Real.log_zero]; exact posLog_nonneg
  · exact (Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))
      (norm_eval_torus_le f θ)).trans (le_max_right _ _)
end ReciprocityTheory.MultiplicativeHeights
