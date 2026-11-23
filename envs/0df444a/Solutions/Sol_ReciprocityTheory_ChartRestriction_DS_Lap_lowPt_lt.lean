-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.lowPt_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:02.393265+00:00
-- url     : https://prove2.me/submissions/3c8973aa-1563-455a-8bdc-af0482d1a73f

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
    (i : ℕ) (x : ℝ) (hi : i < k) (a : Fin (2 * r + k + 1)) (ha : a.val < i) :
    lowPt k r u v b i x a = u ⟨a.val, by omega⟩ - 1 / 2 := by
  have h1 : a.val ≠ i := by omega
  have h2 : a.val < i + 1 ∧ a.val < k := ⟨by omega, by omega⟩
  show (if a.val = i then x else walkPar k r u v b (i + 1) a) = _
  rw [if_neg h1]
  show (if h : a.val < i + 1 ∧ a.val < k then u ⟨a.val, h.2⟩ - 1 / 2 else parLam k r v b a) = _
  rw [dif_pos h2]
end ReciprocityTheory.ChartRestriction.DS.Lap
