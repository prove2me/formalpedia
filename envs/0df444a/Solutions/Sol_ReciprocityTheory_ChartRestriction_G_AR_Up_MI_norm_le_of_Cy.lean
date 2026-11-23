-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.norm_le_of_Cy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:46.929356+00:00
-- url     : https://prove2.me/submissions/dbe06048-c658-4dea-a955-c87ce60557fd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution {y : UpI ι r → ℂ} (hy : y ∈ Cy ι r) (i : UpI ι r) : ‖y i‖ ≤ 2 := by
  by_cases hi : i.1.2.1 = i.1.2.2
  · exact ((hy i).1 hi).2
  · exact ((hy i).2 hi).trans (by norm_num)
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
