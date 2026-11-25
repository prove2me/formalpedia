-- Prove2me | solution 1 for UnipMove.MajH.dot_bot_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:14:50.966842+00:00
-- url     : https://prove2.me/submissions/6d5b4069-07e3-40fa-9445-f293e6204ad2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_DotAddRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_L_np


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
    dot (bot X u) (bot X (col (X.lowBlock Z τ) (Fin.castLE X.p0_le b))) =
      ((Matrix.of (Z τ))ᴴ *ᵥ bot X u) b := by
  simp [dot, bot, col, L_np, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, mul_comm]
end UnipMove.MajH
