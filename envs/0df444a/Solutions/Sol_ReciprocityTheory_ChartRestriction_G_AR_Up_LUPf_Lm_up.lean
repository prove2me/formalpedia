-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_up
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:58.042086+00:00
-- url     : https://prove2.me/submissions/230385af-703c-43b1-b16b-04599bd226aa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfA

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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) (h : i < k) : Lm M i k = 0 := by
  simp only [Lm, Matrix.of_apply]
  have h' : ¬ ((k : ℕ) < i) := by rw [Fin.lt_iff_val_lt_val] at h; omega
  rw [dif_neg h', if_neg (ne_of_gt h)]
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
