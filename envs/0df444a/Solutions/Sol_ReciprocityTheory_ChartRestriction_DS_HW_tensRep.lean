-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.tensRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:46:42.753379+00:00
-- url     : https://prove2.me/submissions/0a05c3cc-c12a-42e7-94f5-d45332900aea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_tensD_units
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_tensTau_cont


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
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution : TensRepStatement := by
  intro n ε Λ T ι _ _ ρ dρ hc hd
  exact ⟨tensTau T ρ, tensD T dρ, tensTau_cont T ρ hc,
    fun X hX γ hγ => tensD_hasDeriv T ρ dρ hX γ hγ (hd X hX γ hγ), fun a b => tensD_units T dρ a b⟩
end ReciprocityTheory.ChartRestriction.DS.HW
