-- Prove2me | solution 1 for UnipMove.MajH.dot_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:07:40.367799+00:00
-- url     : https://prove2.me/submissions/296e28cc-2aff-4926-bff9-7215c6ece4e4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_DotAddRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove UnipMove.MajH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds UnipMove.GraphH NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
namespace UnipMove.MajH
theorem _root_.solution {n : ℕ} (u u' w : Fin n → ℂ) : dot (u + u') w = dot u w + dot u' w := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
end UnipMove.MajH
