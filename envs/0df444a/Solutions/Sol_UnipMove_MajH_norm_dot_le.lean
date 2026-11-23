-- Prove2me | solution 1 for UnipMove.MajH.norm_dot_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:11.00402+00:00
-- url     : https://prove2.me/submissions/76240122-3f02-4f23-b4b0-f97bfe32ac14

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
theorem _root_.solution {n : ℕ} (u w : Fin n → ℂ) : ‖dot u w‖ ≤ en u * en w := by
  have h : dot u w = inner ℂ (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 u) := by
    simp only [dot, PiLp.inner_apply, RCLike.inner_apply, PiLp.toLp_apply]
  rw [h, en, en, mul_comm]
  exact norm_inner_le_norm _ _
end UnipMove.MajH
