-- Prove2me | solution 1 for UnipMove.DeltaValuation.hermLin_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:09.081716+00:00
-- url     : https://prove2.me/submissions/38ac5a89-6eca-40f4-8f34-007bb6aabfc4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_HermLinApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open UnipMove.DeltaValuation
namespace UnipMove.DeltaValuation
theorem _root_.solution {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (K : ℂ) (w v : Fin r → ℂ) :
    hermLin τ G K w v = K * hermC τ G v w := rfl
end UnipMove.DeltaValuation
