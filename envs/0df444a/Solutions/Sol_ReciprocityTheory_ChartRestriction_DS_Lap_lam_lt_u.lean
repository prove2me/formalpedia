-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.lam_lt_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:06.103798+00:00
-- url     : https://prove2.me/submissions/ce011280-0319-4c87-aa08-3dca55970711

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_InterlacesULt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_parLam_of_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_parLam_of_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution {k r : ℕ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ}
    (hI : Interlaces k r u v b) (i : ℕ) (hi : i < k) (hin : i < 2 * r + k + 1) :
    parLam k r v b ⟨i, hin⟩ < u ⟨i, hi⟩ := by
  rcases Nat.lt_or_ge i (k - 1) with h | h
  · rw [parLam_of_lt i hin h]
    exact (hI.1 ⟨i, h⟩).1
  · obtain rfl : i = k - 1 := by omega
    rw [parLam_of_ge (k - 1) hin h]
    have h2 := hI.2 (by omega)
    have e : b ⟨k - 1 - (k - 1), by omega⟩ = b ⟨0, by omega⟩ :=
      congrArg b (Fin.ext (show k - 1 - (k - 1) = 0 by omega))
    rw [e]
    exact h2
end ReciprocityTheory.ChartRestriction.DS.Lap
