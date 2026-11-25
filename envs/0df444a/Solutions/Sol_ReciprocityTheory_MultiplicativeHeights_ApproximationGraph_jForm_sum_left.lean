-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.jForm_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:11:19.075209+00:00
-- url     : https://prove2.me/submissions/196de0a0-fb31-4c73-883f-29811b99fdca

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphB
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_jForm_zero_left
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_jForm_add_left

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
theorem _root_.solution (p : ℕ) {r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ)
    (y : Fin r → ℂ) : jForm p (∑ j ∈ s, f j) y = ∑ j ∈ s, jForm p (f j) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jForm_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, jForm_add_left, ih]
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
