-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.normSq_eq_euc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:55.829061+00:00
-- url     : https://prove2.me/submissions/2f6ace52-d623-45b8-8677-d83cff4d6ad2

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
theorem _root_.solution {r : ℕ} (u : Fin r → ℂ) : normSq u = ‖euc u‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [normSq, euc]
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
