-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.posPart_posPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:05:49.563193+00:00
-- url     : https://prove2.me/submissions/c1aa681c-f981-4c73-98c8-6666c8e25112

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphB

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
theorem _root_.solution (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posPart p (posPart p u) = posPart p u := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
