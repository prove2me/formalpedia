-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:29.935902+00:00
-- url     : https://prove2.me/submissions/68f2b598-5114-4e4b-9f47-0caa595ae08c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_Lm_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_Lm_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
theorem _root_.solution (M : Matrix (Fin n) (Fin n) ℂ) : (Lm M).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun i k h => Lm_up M i k (OrderDual.toDual_lt_toDual.mp h))]
  simp [Lm_diag]
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
