-- Prove2me | solution 1 for UnipMove.GraphH.top_mulVec_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:01:38.174635+00:00
-- url     : https://prove2.me/submissions/0dd29312-43d5-4592-8fb4-166e506ee7e7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Theorems.Thm_UnipMove_GraphH_sum_mul_ext

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace UnipMove.GraphH
theorem _root_.solution (K : Matrix (Fin r) (Fin r) ℂ) (d : Fin X.p0 → ℂ) :
    top X (K *ᵥ ext X d) = blkA X K *ᵥ d := by
  funext a
  exact sum_mul_ext X (fun j => K (Fin.castLE X.p0_le a) j) d
end UnipMove.GraphH
