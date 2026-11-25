-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.jForm_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:25:35.907484+00:00
-- url     : https://prove2.me/submissions/b5037934-ca8e-4825-9f44-c32c7479ac98

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphB
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphC

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
theorem _root_.solution (p : ℕ) {r : ℕ} (x x' y : Fin r → ℂ) :
    jForm p (x + x') y = jForm p x y + jForm p x' y := by
  simp only [ReciprocityTheory.MultiplicativeHeights.jForm, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
