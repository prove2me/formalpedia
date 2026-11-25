-- Prove2me | solution 1 for UnipMove.MajH.conj_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:22:25.126469+00:00
-- url     : https://prove2.me/submissions/dbbd9662-370f-4b5e-8dfb-83c81f169268

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
theorem _root_.solution {n : ℕ} (u w : Fin n → ℂ) : conj (dot u w) = dot w u := by
  simp only [dot, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
end UnipMove.MajH
