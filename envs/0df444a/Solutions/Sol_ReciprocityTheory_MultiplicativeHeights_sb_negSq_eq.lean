-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_negSq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:48:39.2679+00:00
-- url     : https://prove2.me/submissions/d6040770-0a65-4b2e-b684-d738981931c5

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negSq p u = normSq (sbDn p r *ᵥ u) := by
  simp only [negSq, normSq, sbDn, mulVec_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp
end ReciprocityTheory.MultiplicativeHeights
