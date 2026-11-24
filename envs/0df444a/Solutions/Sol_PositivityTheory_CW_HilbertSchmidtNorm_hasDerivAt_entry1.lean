-- Prove2me | solution 1 for PositivityTheory.CW.HilbertSchmidtNorm.hasDerivAt_entry1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:31.024234+00:00
-- url     : https://prove2.me/submissions/adb6b999-71db-495d-8e5f-b3c60989ba66

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_SecondDerivativeHolds
import Theorems.Thm_PositivityTheory_CW_HilbertSchmidtNorm_hasDerivAt_entry

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
theorem _root_.solution (g X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (g * NormedSpace.exp (s • X)) i j)
      ((g * NormedSpace.exp (t • X) * X) i j) t := by
  simpa using hasDerivAt_entry g X 1 t i j
end PositivityTheory.CW.HilbertSchmidtNorm
