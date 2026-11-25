-- Prove2me | solution 1 for UnipMove.GraphH.blkA_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:55:12.290366+00:00
-- url     : https://prove2.me/submissions/7bbb8656-c180-46c7-8a39-a915c5af0e52

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace UnipMove.GraphH
theorem _root_.solution (Z : X.Coord) (τ : X.Ψ) : blkA X (X.lowBlock Z τ) = 1 := by
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  simp only [blkA, Data.lowBlock, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff, Fin.coe_castLE]
  split_ifs <;> first | omega | rfl | simp
end UnipMove.GraphH
