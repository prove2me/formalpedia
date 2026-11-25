-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.posPart_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:14:02.600578+00:00
-- url     : https://prove2.me/submissions/54d8d6ff-792f-4978-bd88-fb65d22f6817

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
theorem _root_.solution (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ∀ j : Fin r, p ≤ (j : ℕ) → posPart p u j = 0 := fun j hj => by
  simp [posPart, not_lt.mpr hj]
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
