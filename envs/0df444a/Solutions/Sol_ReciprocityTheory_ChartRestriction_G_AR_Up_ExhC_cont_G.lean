-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC.cont_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:08.366719+00:00
-- url     : https://prove2.me/submissions/da140648-31d2-4e3f-afbc-e749480686e2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_cont_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_cont_entry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_zPart_apply


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
theorem _root_.solution : Continuous fun v : V (nD f p q + N') => ∏ k, dk (zPart v) k := by
  refine continuous_finsetProd _ fun k _ => Complex.continuous_re.comp ?_
  have hc := cont_entry (fun v : V (nD f p q + N') => zPart v)
    (fun i => by simp only [zPart_apply]; exact cont_coord _) k
  exact (continuous_pi fun a => continuous_pi fun b => hc a b).matrix_det
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
