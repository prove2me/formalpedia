-- Prove2me | solution 1 for UnipMove.GraphH.fin_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:00:36.923973+00:00
-- url     : https://prove2.me/submissions/ef9fc16f-07b3-46ba-97a0-82f98da95b53

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
theorem _root_.solution (i : Fin r) :
    (∃ a : Fin X.p0, i = Fin.castLE X.p0_le a) ∨ ∃ m : Fin (r - X.p0), i = nI X m := by
  by_cases h : (i : ℕ) < X.p0
  · exact Or.inl ⟨⟨i, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨(i : ℕ) - X.p0, by have := i.isLt; omega⟩, Fin.ext ?_⟩
    show (i : ℕ) = X.p0 + ((i : ℕ) - X.p0)
    omega
end UnipMove.GraphH
