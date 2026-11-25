-- Prove2me | solution 1 for UnipMove.DeltaValuation.O_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:04.756246+00:00
-- url     : https://prove2.me/submissions/8d756424-bbe5-4d27-864d-601e09205715

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
theorem _root_.solution {r : ℕ} (β : 𝓞 E) (v : Fin r → E) : β • v = (β : E) • v := rfl
end UnipMove.DeltaValuation
