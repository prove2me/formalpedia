-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.no_cross
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:06.723787+00:00
-- url     : https://prove2.me/submissions/d9acf1b8-94b9-4c16-be0a-b9fd90fc9df1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_InterlacesULt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_u_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_u_lt_v
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_parLam_of_lt

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
    (hI : Interlaces k r u v b) (i : ℕ) (hi : i < k) (hin : i < 2 * r + k + 1) (y : ℝ)
    (h1 : parLam k r v b ⟨i, hin⟩ + 1 ≤ y) (h2 : y ≤ u ⟨i, hi⟩ - 1 / 2) (l : Fin k) :
    u l ≠ y - 1 / 2 := by
  intro heq
  rcases lt_trichotomy l.val i with hl | hl | hl
  · have h3 := u_lt hI l ⟨i, hi⟩ hl
    linarith
  · have hl' : l = ⟨i, hi⟩ := Fin.ext hl
    subst hl'
    linarith
  · have hik : i < k - 1 := by have := l.isLt; omega
    have h3 := u_lt_v hI i hik l hl
    rw [parLam_of_lt i hin hik] at h1
    linarith
end ReciprocityTheory.ChartRestriction.DS.Lap
