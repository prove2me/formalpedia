-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.lowPt_gt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:10.36896+00:00
-- url     : https://prove2.me/submissions/724c61a3-d889-4f15-b87e-a7c37f3b8e30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_InterlacesULt

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
    (i : ℕ) (x : ℝ) (a : Fin (2 * r + k + 1)) (ha : i < a.val) :
    lowPt k r u v b i x a = parLam k r v b a := by
  have h1 : a.val ≠ i := by omega
  have h2 : ¬ (a.val < i + 1 ∧ a.val < k) := fun h' => absurd h'.1 (by omega)
  show (if a.val = i then x else walkPar k r u v b (i + 1) a) = _
  rw [if_neg h1]
  show (if h : a.val < i + 1 ∧ a.val < k then u ⟨a.val, h.2⟩ - 1 / 2 else parLam k r v b a) = _
  rw [dif_neg h2]
end ReciprocityTheory.ChartRestriction.DS.Lap
