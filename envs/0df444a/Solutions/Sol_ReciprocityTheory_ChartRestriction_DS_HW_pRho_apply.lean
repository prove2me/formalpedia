-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.pRho_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:58:05.527552+00:00
-- url     : https://prove2.me/submissions/078afaa7-aa47-44d6-b0f9-8d49c244bc46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Unique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PrhoEntryHasDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open scoped Kronecker
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
variable {ε : Fin n → Bool} {β : Bool}
variable (ε β)
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (k : KG ε) (p q : pIdx ε β) :
    ((pRho ε β k : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) p q =
      toMK k p.1.1 q.1.1 * star (toMK k p.1.2 q.1.2) := rfl
end ReciprocityTheory.ChartRestriction.DS.HW
