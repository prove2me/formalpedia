-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.pPlus_pWt_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:02:31.435081+00:00
-- url     : https://prove2.me/submissions/1ad1addc-1480-477e-ad4d-7262beeffc57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Weight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PPlusPWtInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pPlus_fst_ne_snd

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
theorem _root_.solution (ε : Fin n → Bool) (β : Bool) : Function.Injective (pWt ε β) := by
  intro p q h
  have hp := pPlus_fst_ne_snd p
  have e1 := congrFun h p.1.1
  have e2 := congrFun h p.1.2
  simp only [pWt, Pi.sub_apply, Pi.single_apply] at e1 e2
  rw [if_pos trivial, if_neg hp] at e1
  rw [if_neg (Ne.symm hp), if_pos trivial] at e2
  have h1 : p.1.1 = q.1.1 := by
    by_contra hne
    rw [if_neg hne] at e1
    split_ifs at e1 <;> norm_num at e1
  have h2 : p.1.2 = q.1.2 := by
    by_contra hne
    rw [if_neg hne] at e2
    split_ifs at e2 <;> norm_num at e2
  exact Subtype.ext (Prod.ext h1 h2)
end ReciprocityTheory.ChartRestriction.DS.HW
