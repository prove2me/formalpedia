-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.weylSum_card_pIdx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:12:41.240042+00:00
-- url     : https://prove2.me/submissions/e1d55e9d-0c30-47ff-be26-ed5d856ae279

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_BlockSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylSum_pIdx

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (β : Bool) :
    (Nat.card (pIdx ε β) : ℝ) = ((univ.filter (fun i => ε i = β)).card : ℝ) *
      ((univ.filter (fun j => ε j = !β)).card : ℝ) := by
  have h := weylSum_pIdx ε β (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h
  rw [Nat.card_eq_fintype_card, ← h]
end ReciprocityTheory.ChartRestriction.DS.HW
