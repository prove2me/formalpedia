-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.card_same_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:14.59614+00:00
-- url     : https://prove2.me/submissions/1951f54b-3427-4657-a967-c48ba5cb181a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => ε b = ε a).card = (univ.filter fun b => b < a ∧ ε b = ε a).card + 1 +
      (univ.filter fun b => a < b ∧ ε b = ε a).card := by
  rw [card_filter, card_filter, card_filter,
    show (1:ℕ) = ∑ b : Fin n, if b = a then 1 else 0 by simp, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy b a with h | rfl | h
  · simp [h, h.ne, not_lt_of_gt h]
  · simp
  · simp [h, h.ne', not_lt_of_gt h]
end ReciprocityTheory.ChartRestriction.DS
