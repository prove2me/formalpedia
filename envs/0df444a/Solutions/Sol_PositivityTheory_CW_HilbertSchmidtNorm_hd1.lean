-- Prove2me | solution 1 for PositivityTheory.CW.HilbertSchmidtNorm.hd1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:32:41.046011+00:00
-- url     : https://prove2.me/submissions/7d7681ba-a861-44df-9a48-1dbe1bf29a58

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_SecondDerivativeHolds
import Theorems.Thm_PositivityTheory_CW_HilbertSchmidtNorm_hasDerivAt_entry1

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
theorem _root_.solution (g X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => hs2 (g * NormedSpace.exp (s • X)))
      (∑ i, ∑ j, 2 * inner ℝ ((g * NormedSpace.exp (t • X)) i j) ((g * NormedSpace.exp (t • X) * X) i j)) t := by
  unfold hs2
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  exact (hasDerivAt_entry1 g X t i j).norm_sq
end PositivityTheory.CW.HilbertSchmidtNorm
