-- Prove2me | solution 1 for PositivityTheory.CW.HilbertSchmidtNorm.hd2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:27:47.331849+00:00
-- url     : https://prove2.me/submissions/f34252fc-3df2-4af1-9793-91976adce0e9

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_SecondDerivativeHolds
import Theorems.Thm_PositivityTheory_CW_HilbertSchmidtNorm_hasDerivAt_entry
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
    HasDerivAt (fun s : ℝ => ∑ i, ∑ j, 2 * inner ℝ ((g * NormedSpace.exp (s • X)) i j)
        ((g * NormedSpace.exp (s • X) * X) i j))
      (∑ i, ∑ j, 2 * (inner ℝ ((g * NormedSpace.exp (t • X)) i j) ((g * NormedSpace.exp (t • X) * X * X) i j) +
        inner ℝ ((g * NormedSpace.exp (t • X) * X) i j) ((g * NormedSpace.exp (t • X) * X) i j))) t := by
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  exact ((hasDerivAt_entry1 g X t i j).inner ℝ (hasDerivAt_entry g X X t i j)).const_mul 2
end PositivityTheory.CW.HilbertSchmidtNorm
