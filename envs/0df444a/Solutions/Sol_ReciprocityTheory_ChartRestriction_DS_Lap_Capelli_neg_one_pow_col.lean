-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.neg_one_pow_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:57.069701+00:00
-- url     : https://prove2.me/submissions/3f515e22-2f75-4dfc-9544-e3d59ccb4714

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowColA

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution (a b c : ℕ) :
    (-1 : ℂ) ^ (a + b) * (-1 : ℂ) ^ (b + c + 1) = (-1 : ℂ) ^ (a + c + 1) := by
  rw [← pow_add, show a + b + (b + c + 1) = (a + c + 1) + 2 * b by ring, pow_add, pow_mul]
  simp
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
