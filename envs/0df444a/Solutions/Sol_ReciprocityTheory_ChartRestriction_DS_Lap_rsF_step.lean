-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.rsF_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:26:52.886639+00:00
-- url     : https://prove2.me/submissions/38636319-35a0-42ce-81c3-46cdc77aed9c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_RsParLamMinus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_rsG_step
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_rsG_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution (k r : ℕ) (U B : ℕ → ℝ) (h : ℝ) (t j m x : ℕ) (hk : 1 ≤ k) (hm : m ≤ j * t)
    (hBlt : ∀ q, q + 1 < 2 * r + 2 → B q < B (q + 1))
    (hBgap : ∀ q, q + 1 < 2 * r + 2 → h ≤ B (q + 1) - B q)
    (hUlt : ∀ x, x + 1 < k → U (x + 1) < U x) (hUhalf : -B 0 ≤ U (k - 1) - 1 / 2)
    (hx : x + 1 < 2 * r + k + 1) :
    rsF k U B t j m (x + 1) < rsF k U B t j m x ∧
      (k - 1 ≤ x → h ≤ rsF k U B t j m x - rsF k U B t j m (x + 1)) := by
  by_cases hx1 : x + 1 < k
  · have hx0 : x < k := by omega
    rw [rsF, rsF, if_pos hx1, if_pos hx0]
    exact ⟨by linarith [hUlt x hx1], fun h' => absurd h' (by omega)⟩
  · by_cases hx0 : x < k
    · have hxk : x = k - 1 := by omega
      have e : x + 1 - (k - 1) = 1 := by omega
      rw [rsF, rsF, if_neg hx1, if_pos hx0, e]
      have hle := rsG_le B t j m 1 hm
      have hb01 : B 0 < B 1 := hBlt 0 (by omega)
      have hg01 : h ≤ B 1 - B 0 := hBgap 0 (by omega)
      have hU : U x = U (k - 1) := by rw [hxk]
      constructor
      · linarith
      · intro _
        linarith
    · have hq : x - (k - 1) + 1 < 2 * r + 2 := by omega
      have e : x + 1 - (k - 1) = x - (k - 1) + 1 := by omega
      rw [rsF, rsF, if_neg hx1, if_neg hx0, e]
      obtain ⟨h1, h2⟩ := rsG_step B h t j m (x - (k - 1)) (2 * r + 2) hm hBlt hBgap hq
      exact ⟨h1, fun _ => h2⟩
end ReciprocityTheory.ChartRestriction.DS.Lap
