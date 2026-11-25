-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.pPlus_card_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:12:41.387956+00:00
-- url     : https://prove2.me/submissions/26042cb5-81a6-4ba1-be60-229b5a4fcc3b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Weight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PPlusPWtInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pPlus_pWt_injective

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (β : Bool) (Λ : Fin n → ℝ) (p : pIdx ε β) :
    Nat.card {q : pIdx ε β // Λ + pWt ε β p = Λ + pWt ε β q} = 1 :=
  Nat.card_eq_one_iff_exists.mpr
    ⟨⟨p, rfl⟩, fun q => Subtype.ext (pPlus_pWt_injective ε β (add_left_cancel q.2).symm)⟩
end ReciprocityTheory.ChartRestriction.DS.HW
