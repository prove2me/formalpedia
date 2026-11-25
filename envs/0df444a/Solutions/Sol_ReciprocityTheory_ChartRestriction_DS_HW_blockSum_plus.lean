-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.blockSum_plus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:18:47.177335+00:00
-- url     : https://prove2.me/submissions/77901e96-53f7-4f39-a2e0-19789540e8b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_BlockSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pieri_sum_finset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_block_filter_eq_erase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open Polynomial Finset
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (β : Bool) (u : Fin n → ℝ)
    (hu : ∀ a b, ε a = β → ε b = β → u a = u b → a = b) :
    ∑ s ∈ univ.filter (fun s => ε s = β), ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s),
      (u s - u b + 1) / (u s - u b) = ((univ.filter (fun s => ε s = β)).card : ℝ) := by
  rw [Finset.sum_congr rfl (fun s hs => by rw [block_filter_eq_erase ε β (Finset.mem_filter.mp hs).2])]
  exact pieri_sum_finset _ u (fun a ha b hb h =>
    hu a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 h)
end ReciprocityTheory.ChartRestriction.DS.HW
