-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhE_sqNorm_nonneg__56844cb7c596
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:23.87343+00:00
-- url     : https://prove2.me/submissions/e2f89335-3e22-42f3-99ba-d0bf443ab3d2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
variable {f p q N' : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
theorem _root_.solution {m : ℕ} (g : Fin m → ℂ) : 0 ≤ sqNorm g :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
