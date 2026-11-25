-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.walkPar_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:12:36.63004+00:00
-- url     : https://prove2.me/submissions/05a92b4a-c8d1-4482-84f9-2a35075e0f4d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_InterlacesULt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lowPt_at

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
    (i : ℕ) (hi : i < k) (hin : i < 2 * r + k + 1) (c : ℝ) :
    walkPar k r u v b (i + 1) + c • Pi.single (⟨i, hin⟩ : Fin (2 * r + k + 1)) (1 : ℝ) =
      lowPt k r u v b i (u ⟨i, hi⟩ - 1 / 2 + c) := by
  funext a
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases ha : a.val = i
  · obtain rfl : a = ⟨i, hin⟩ := Fin.ext ha
    rw [lowPt_at, Pi.single_eq_same, mul_one]
    have h2 : i < i + 1 ∧ i < k := ⟨Nat.lt_succ_self i, hi⟩
    show (if h : i < i + 1 ∧ i < k then u ⟨i, h.2⟩ - 1 / 2 else parLam k r v b ⟨i, hin⟩) + c = _
    rw [dif_pos h2]
  · have hne : a ≠ ⟨i, hin⟩ := fun h => ha (congrArg Fin.val h)
    rw [Pi.single_apply, if_neg hne, mul_zero, add_zero]
    show _ = (if a.val = i then _ else walkPar k r u v b (i + 1) a)
    rw [if_neg ha]
end ReciprocityTheory.ChartRestriction.DS.Lap
