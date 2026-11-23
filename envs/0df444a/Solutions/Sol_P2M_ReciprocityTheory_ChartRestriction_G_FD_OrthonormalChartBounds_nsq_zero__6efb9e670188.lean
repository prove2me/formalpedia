-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_nsq_zero__6efb9e670188
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:21.491944+00:00
-- url     : https://prove2.me/submissions/84111bba-c196-4c63-b2dd-94af1cb34eb4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermCOrthonormalCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution {n : ℕ} : nsq (0 : Fin n → ℂ) = 0 := by
  simp [nsq]
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
