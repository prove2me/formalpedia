-- Prove2me | solution 1 for UnipMove.GraphH.blkB_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:55:21.953157+00:00
-- url     : https://prove2.me/submissions/848e6e04-1b97-4b1d-bd53-f3016f095d99

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
theorem _root_.solution (Z : X.Coord) (τ : X.Ψ) : blkB X (X.lowBlock Z τ) = Matrix.of (Z τ) := by
  ext m b
  have hb := b.isLt
  have hne : X.p0 + (m : ℕ) ≠ (b : ℕ) := by omega
  first
    | simp [blkB, Data.lowBlock, nI, Fin.ext_iff, hne, hb]
    | (simp only [blkB, Data.lowBlock, Matrix.of_apply, Fin.ext_iff, Fin.coe_castLE, nI]
       split_ifs <;> first | (simp_all; done) | omega | (congr 1 <;> ext <;> simp))
end UnipMove.GraphH
