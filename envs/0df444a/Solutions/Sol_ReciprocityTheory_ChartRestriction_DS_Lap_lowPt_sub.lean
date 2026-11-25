-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.lowPt_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:25.682045+00:00
-- url     : https://prove2.me/submissions/208eb782-2c38-4836-ad95-03329bc77854

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
    (i : ℕ) (hin : i < 2 * r + k + 1) (y : ℝ) :
    lowPt k r u v b i y - Pi.single (⟨i, hin⟩ : Fin (2 * r + k + 1)) (1 : ℝ) =
      lowPt k r u v b i (y - 1) := by
  funext a
  rw [Pi.sub_apply]
  by_cases ha : a.val = i
  · obtain rfl : a = ⟨i, hin⟩ := Fin.ext ha
    rw [lowPt_at, lowPt_at, Pi.single_eq_same]
  · have hne : a ≠ ⟨i, hin⟩ := fun h => ha (congrArg Fin.val h)
    rw [Pi.single_apply, if_neg hne, sub_zero]
    show (if a.val = i then y else walkPar k r u v b (i + 1) a) =
      (if a.val = i then y - 1 else walkPar k r u v b (i + 1) a)
    rw [if_neg ha, if_neg ha]
end ReciprocityTheory.ChartRestriction.DS.Lap
