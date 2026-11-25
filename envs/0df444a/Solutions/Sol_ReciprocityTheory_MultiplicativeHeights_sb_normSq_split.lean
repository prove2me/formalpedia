-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_normSq_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:27:44.782317+00:00
-- url     : https://prove2.me/submissions/3383bd13-b607-458f-abf6-8e7a09fcee23

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallC

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
open Matrix Module
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (p : ℕ) {r : ℕ} (v : Fin r → ℂ) : normSq v = posSq p v + negSq p v := by
  unfold normSq posSq negSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp
end ReciprocityTheory.MultiplicativeHeights
