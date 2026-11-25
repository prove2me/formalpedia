-- Prove2me | solution 1 for UnipMove.MajH.nsq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:52:53.642474+00:00
-- url     : https://prove2.me/submissions/edefd022-150d-4a4a-86a1-31c270e96ce6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_DotAddRight
import Theorems.Thm_UnipMove_MajH_dot_add_left
import Theorems.Thm_UnipMove_MajH_dot_add_right
import Theorems.Thm_UnipMove_MajH_re_dot_comm
import Theorems.Thm_UnipMove_MajH_re_dot_self

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
theorem _root_.solution {n : ℕ} (u w : Fin n → ℂ) : nsq (u + w) = nsq u + nsq w + 2 * (dot u w).re := by
  rw [← re_dot_self, ← re_dot_self u, ← re_dot_self w, dot_add_left, dot_add_right,
    dot_add_right]
  simp only [Complex.add_re]
  rw [re_dot_comm w u]
  ring
end UnipMove.MajH
