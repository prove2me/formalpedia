-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.weylSum_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:22:52.20534+00:00
-- url     : https://prove2.me/submissions/48785c0c-1533-45aa-bc70-639fd7b011f2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_BlockSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_rhoC_sub_ge_one


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
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (hΛ : KDom ε Λ) (β : Bool) :
    ∀ a b, ε a = β → ε b = β → (Λ + rhoC ε) a = (Λ + rhoC ε) b → a = b := by
  intro a b ha hb h
  have he : ε a = ε b := ha.trans hb.symm
  simp only [Pi.add_apply] at h
  rcases lt_trichotomy a b with hab | rfl | hab
  · have h1 := rhoC_sub_ge_one ε hab he
    have h2 := hΛ a b hab he
    linarith
  · rfl
  · have h1 := rhoC_sub_ge_one ε hab he.symm
    have h2 := hΛ b a hab he.symm
    linarith
end ReciprocityTheory.ChartRestriction.DS.HW
