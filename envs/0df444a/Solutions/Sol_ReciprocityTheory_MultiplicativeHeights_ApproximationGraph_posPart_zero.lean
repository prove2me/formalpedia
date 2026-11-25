-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.posPart_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:17:05.724113+00:00
-- url     : https://prove2.me/submissions/dfb8dba3-4cbd-49df-9d7a-b5d793dff807

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
theorem _root_.solution (p : ℕ) {r : ℕ} : posPart p (0 : Fin r → ℂ) = 0 := by
  ext k
  simp [posPart]
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
