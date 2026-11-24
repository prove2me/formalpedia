-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.pPlus_fst_ne_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:38:32.144946+00:00
-- url     : https://prove2.me/submissions/1f089974-f59a-4474-bf91-d547a71eff1a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Weight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PPlusPWtInjective

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
theorem _root_.solution {ε : Fin n → Bool} {β : Bool} (p : pIdx ε β) : p.1.1 ≠ p.1.2 := by
  intro h
  obtain ⟨h1, h2⟩ := p.2
  rw [h] at h1
  rw [h1] at h2
  cases β <;> simp at h2
end ReciprocityTheory.ChartRestriction.DS.HW
