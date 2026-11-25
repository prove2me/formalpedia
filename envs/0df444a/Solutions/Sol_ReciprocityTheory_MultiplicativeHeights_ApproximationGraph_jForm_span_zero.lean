-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.jForm_span_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:24:45.721804+00:00
-- url     : https://prove2.me/submissions/60fc0270-982b-49d4-b086-80c25eda4ca9

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphB
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_jForm_smul_left
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_jForm_sum_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
open ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
theorem _root_.solution (p : ℕ) {r : ℕ} (X : Fin r → Fin r → ℂ) (y : Fin r → ℂ)
    (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) (w : Fin r → ℂ)
    (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) : jForm p (∑ j, w j • X j) y = 0 := by
  rw [jForm_sum_left]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [jForm_smul_left]
  by_cases hj : (j : ℕ) < p
  · rw [hy j hj, mul_zero]
  · rw [hw j (not_lt.mp hj), map_zero, zero_mul]
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
