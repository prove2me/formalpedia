-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.signedOrder_iff_not_swap_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:04.514817+00:00
-- url     : https://prove2.me/submissions/21b8400a-30b8-4838-9b3a-7caf28c2b9bc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero

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
theorem _root_.solution (ε : Fin n → Bool) (a b : Fin n) (h : a ≠ b) : wdP ε a b ↔ ¬ wdP ε b a := by
  unfold wdP
  rcases lt_or_gt_of_ne h with h | h
  · by_cases he : ε a = ε b
    · simp [h, lt_asymm h, he]
    · simp [h, lt_asymm h, he, Ne.symm he]
  · by_cases he : ε a = ε b
    · simp [h, lt_asymm h, he]
    · simp [h, lt_asymm h, he, Ne.symm he]
end ReciprocityTheory.ChartRestriction.DS
