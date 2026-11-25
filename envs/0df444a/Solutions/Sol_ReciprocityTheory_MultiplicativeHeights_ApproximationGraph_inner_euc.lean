-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.inner_euc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:25:31.417042+00:00
-- url     : https://prove2.me/submissions/6baad9d0-a8e1-41ad-a6f7-1f182e691975

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
theorem _root_.solution {r : ℕ} (x y : Fin r → ℂ) : inner ℂ (euc x) (euc y) = ∑ k, conj (x k) * y k := by
  simp [euc, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
