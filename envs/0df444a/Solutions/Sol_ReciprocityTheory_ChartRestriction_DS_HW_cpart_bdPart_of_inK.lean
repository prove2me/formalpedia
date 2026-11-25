-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.cpart_bdPart_of_inK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:00.166659+00:00
-- url     : https://prove2.me/submissions/49ceaafc-2375-4c25-bcac-ea9852a09576

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelCext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_inK_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    cpart1 ε (bdPart ε X) = X ∧ cpart2 ε (bdPart ε X) = 0 := by
  refine ⟨?_, ?_⟩ <;> ext a b
  · obtain ⟨h0, hs⟩ := inK_apply ε hX a b
    rw [cpart1_bdPart_apply]
    split_ifs with h
    · rw [hs]; ring
    · exact (h0 h).symm
  · obtain ⟨h0, hs⟩ := inK_apply ε hX a b
    rw [Matrix.zero_apply, cpart2_bdPart_apply]
    split_ifs with h
    · rw [hs]; ring
    · rfl
end ReciprocityTheory.ChartRestriction.DS.HW
