-- Prove2me | solution 1 for UnipMove.GraphH.en_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:00:16.888564+00:00
-- url     : https://prove2.me/submissions/5cecc9c9-9293-4bf8-a467-0e83bdd69f7d

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
section
namespace UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
private lemma nsq_nonneg_unipotent_moves {n : ℕ} (v : Fin n → ℂ) : 0 ≤ nsq v :=
  Finset.sum_nonneg fun j _ => sq_nonneg _
section Blocks
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
end Blocks
section Frames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
end Frames
end
end UnipMove.GraphH
namespace UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField
end UnipMove
end

set_option autoImplicit false
open UnipMove UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
namespace UnipMove.GraphH
theorem _root_.solution {n : ℕ} (v : Fin n → ℂ) : en v ^ 2 = nsq v := by
  have e : en v = Real.sqrt (nsq v) := by
    unfold en nsq
    first
      | (rw [EuclideanSpace.norm_eq]; rfl)
      | (rw [EuclideanSpace.norm_eq]; simp)
      | simp [EuclideanSpace.norm_eq]
  rw [e, Real.sq_sqrt (nsq_nonneg_unipotent_moves v)]
end UnipMove.GraphH
