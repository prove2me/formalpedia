-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.euc_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:24:50.434876+00:00
-- url     : https://prove2.me/submissions/9da99b1c-d15d-4f2b-8869-853128778ec3

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_euc_add
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_euc_zero

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
theorem _root_.solution {r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) :
    euc (∑ j ∈ s, f j) = ∑ j ∈ s, euc (f j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact euc_zero
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, euc_add, ih]
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
