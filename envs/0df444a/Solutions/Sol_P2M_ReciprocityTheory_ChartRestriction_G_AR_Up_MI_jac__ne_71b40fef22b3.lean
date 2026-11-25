-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_jac__ne_71b40fef22b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:14.924954+00:00
-- url     : https://prove2.me/submissions/f65593c1-e1ab-4a5a-a9d6-38713a4637c9

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
theorem _root_.solution (β : ι → Matrix (Fin r) (Fin r) ℂ) (hd : ∀ τ b, β τ b b ≠ 0) : jacβ β ≠ 0 := by
  unfold jacβ
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  split_ifs
  · exact hd _ _
  · exact one_ne_zero
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
