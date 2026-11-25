-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.sum_Ico_tele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:55.361228+00:00
-- url     : https://prove2.me/submissions/fbbaf7e4-817d-4e9d-b895-8dba57b7e573

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (f : ℕ → ℝ) {b : ℕ} : ∀ m, b ≤ m → ∑ i ∈ Finset.Ico b m, (f i - f (i + 1)) = f b - f m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih => rw [Finset.sum_Ico_succ_top hm, ih]; ring
end ReciprocityTheory.ChartRestriction.DS.S7
