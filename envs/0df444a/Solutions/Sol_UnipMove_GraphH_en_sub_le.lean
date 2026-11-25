-- Prove2me | solution 1 for UnipMove.GraphH.en_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:00:21.783053+00:00
-- url     : https://prove2.me/submissions/aa63284d-c0f3-42dd-9d27-4066058616f7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
namespace UnipMove.GraphH
theorem _root_.solution {n : ℕ} (u v : Fin n → ℂ) : en (u - v) ≤ en u + en v := by
  unfold en
  first
    | (rw [WithLp.toLp_sub]; exact norm_sub_le _ _)
    | exact norm_sub_le _ _
    | simpa using norm_sub_le (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 v)
end UnipMove.GraphH
