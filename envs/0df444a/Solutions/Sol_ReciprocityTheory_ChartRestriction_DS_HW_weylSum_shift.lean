-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.weylSum_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:32:43.787404+00:00
-- url     : https://prove2.me/submissions/404a0b56-0e5f-4402-9e46-2df1771d8647

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_BlockSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylSum_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylSum_card_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylK_add_smul_single


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) (c : ℝ)
    (hc : ∀ β : Bool, ∑ s ∈ univ.filter (fun s => ε s = β), ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s),
      ((Λ + rhoC ε) s - (Λ + rhoC ε) b + c) / ((Λ + rhoC ε) s - (Λ + rhoC ε) b) =
        ((univ.filter (fun s => ε s = β)).card : ℝ)) :
    ∑ s, weylK ε (Λ + c • (Pi.single s (1 : ℝ) : Fin n → ℝ)) = (n : ℝ) * weylK ε Λ := by
  simp only [weylK_add_smul_single ε Λ hΛ]
  rw [← Finset.mul_sum, weylSum_split ε, hc true, hc false, weylSum_card_split]
  ring
end ReciprocityTheory.ChartRestriction.DS.HW
