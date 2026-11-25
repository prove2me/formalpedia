-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.wPart_wPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:40:07.024665+00:00
-- url     : https://prove2.me/submissions/08b3867d-d4f1-4f91-967c-6b83e754b6ae

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution (r m : ℕ) (i : Fin r) : wPart r m (wPart r m i) = i := by
  have hi := i.isLt
  unfold wPart
  by_cases h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m
  · rw [if_pos h, if_pos (by simp only [Fin.val_rev]; omega), Fin.rev_rev]
  · rw [if_neg h, if_neg h]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
