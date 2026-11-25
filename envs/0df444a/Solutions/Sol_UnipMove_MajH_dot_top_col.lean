-- Prove2me | solution 1 for UnipMove.MajH.dot_top_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:04.738618+00:00
-- url     : https://prove2.me/submissions/b93919db-b4bc-4e5b-ac55-ddb0e8ac63c7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_DotAddRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_L_pp


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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace UnipMove.MajH
theorem _root_.solution (Z : X.Coord) (τ : X.Ψ) (u : Fin r → ℂ) (b : Fin X.p0) :
    dot (top X u) (top X (col (X.lowBlock Z τ) (Fin.castLE X.p0_le b))) = top X u b := by
  simp [dot, top, col, L_pp]
end UnipMove.MajH
