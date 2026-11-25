-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.sum_norm_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:17:07.914483+00:00
-- url     : https://prove2.me/submissions/9b66cdb6-fd28-4e99-954f-4190a05c23c7

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphA

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
theorem _root_.solution {r : ℕ} (w : Fin r → ℂ) : ∑ j, ‖w j‖ ≤ √(r : ℝ) * ‖euc w‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin r => (1 : ℝ)) (fun j => ‖w j‖)
  rw [EuclideanSpace.norm_eq]
  simpa [euc] using h
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
