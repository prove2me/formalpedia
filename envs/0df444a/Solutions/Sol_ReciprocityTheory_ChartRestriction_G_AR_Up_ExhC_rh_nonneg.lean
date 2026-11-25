-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC.rh_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:42:05.359578+00:00
-- url     : https://prove2.me/submissions/81fffc04-4407-4ad6-862c-f59256d6a6a2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhA_det_re_le_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhA_det_re_pos_im


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
variable {f p q N' : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
theorem _root_.solution {w : V (nD f p q)} (hw : w ∈ Dset f p q) : 0 ≤ rh w := by
  unfold rh
  rw [neg_nonneg]
  exact Finset.sum_nonpos fun k _ => Real.log_nonpos (det_re_pos_im (hw k)).1.le (det_re_le_one (hw k))
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
