-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_posSq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:47:33.699567+00:00
-- url     : https://prove2.me/submissions/f4fd366b-8039-4aed-ba95-1531e93a7029

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
theorem _root_.solution (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posSq p u = normSq (sbDp p r *ᵥ u) := by
  simp only [posSq, normSq, sbDp, mulVec_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp
end ReciprocityTheory.MultiplicativeHeights
