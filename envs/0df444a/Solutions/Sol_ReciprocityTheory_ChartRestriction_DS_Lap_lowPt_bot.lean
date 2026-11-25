-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.lowPt_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:23.190933+00:00
-- url     : https://prove2.me/submissions/d770d89d-eeaf-47ef-a56e-2be206c25d2f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_InterlacesULt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lowPt_at
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lowPt_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lowPt_gt

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
theorem _root_.solution {k r : ℕ} (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (i : ℕ) (hi : i < k) (hin : i < 2 * r + k + 1) :
    lowPt k r u v b i (parLam k r v b ⟨i, hin⟩) = walkPar k r u v b i := by
  funext a
  rcases lt_trichotomy a.val i with h | h | h
  · rw [lowPt_lt (u := u) (v := v) (b := b) i (parLam k r v b ⟨i, hin⟩) hi a h]
    have h2 : a.val < i ∧ a.val < k := ⟨h, by omega⟩
    show _ = (if h : a.val < i ∧ a.val < k then u ⟨a.val, h.2⟩ - 1 / 2 else parLam k r v b a)
    rw [dif_pos h2]
  · obtain rfl : a = ⟨i, hin⟩ := Fin.ext h
    rw [lowPt_at]
    have h2 : ¬ (i < i ∧ i < k) := fun h' => lt_irrefl i h'.1
    show _ = (if h : i < i ∧ i < k then u ⟨i, h.2⟩ - 1 / 2 else parLam k r v b ⟨i, hin⟩)
    rw [dif_neg h2]
  · rw [lowPt_gt (u := u) (v := v) (b := b) i (parLam k r v b ⟨i, hin⟩) a h]
    have h2 : ¬ (a.val < i ∧ a.val < k) := fun h' => absurd h'.1 (by omega)
    show _ = (if h : a.val < i ∧ a.val < k then u ⟨a.val, h.2⟩ - 1 / 2 else parLam k r v b a)
    rw [dif_neg h2]
end ReciprocityTheory.ChartRestriction.DS.Lap
