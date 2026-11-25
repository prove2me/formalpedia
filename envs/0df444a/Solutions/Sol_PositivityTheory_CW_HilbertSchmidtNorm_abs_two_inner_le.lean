-- Prove2me | solution 1 for PositivityTheory.CW.HilbertSchmidtNorm.abs_two_inner_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:32:37.77655+00:00
-- url     : https://prove2.me/submissions/fef66e95-7a40-4ca0-9a08-27a16a22c3f1

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_SecondDerivativeHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.HilbertSchmidtNorm
variable {n : ℕ}
namespace PositivityTheory.CW.HilbertSchmidtNorm
theorem _root_.solution (M N : Matrix (Fin n) (Fin n) ℂ) :
    |∑ i, ∑ j, 2 * inner ℝ (M i j) (N i j)| ≤ hs2 M + hs2 N := by
  unfold hs2
  rw [← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have := abs_real_inner_le_norm (M i j) (N i j)
  rw [abs_mul, abs_two]
  nlinarith [sq_nonneg (‖M i j‖ - ‖N i j‖)]
end PositivityTheory.CW.HilbertSchmidtNorm
