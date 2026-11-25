-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.lam_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:02.464993+00:00
-- url     : https://prove2.me/submissions/9d990728-695e-4be9-beed-611b418562f8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_InterlacesULt
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
theorem _root_.solution {k r : ℕ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} {h : ℝ} (hk : 1 ≤ k)
    (hG : LowGaps r b h) (a : Fin (2 * r + k + 1)) (ha : a.val + 1 < 2 * r + k + 1)
    (hka : k - 1 ≤ a.val) :
    h ≤ parLam k r v b a - parLam k r v b ⟨a.val + 1, ha⟩ := by
  have haa := a.isLt
  have hj : a.val - (k - 1) + 1 < 2 * r + 2 := by omega
  have h1 : parLam k r v b a = -b ⟨a.val - (k - 1), by omega⟩ := parLam_of_ge a.val a.isLt hka
  have hg : h ≤ b ⟨a.val - (k - 1) + 1, hj⟩ - b ⟨a.val - (k - 1), by omega⟩ :=
    hG ⟨a.val - (k - 1), by omega⟩ hj
  have e : (⟨a.val - (k - 1) + 1, hj⟩ : Fin (2 * r + 2)) = ⟨a.val + 1 - (k - 1), by omega⟩ :=
    Fin.ext (show a.val - (k - 1) + 1 = a.val + 1 - (k - 1) by omega)
  rw [e] at hg
  rw [h1, parLam_of_ge (a.val + 1) ha (by omega)]
  linarith
end ReciprocityTheory.ChartRestriction.DS.Lap
