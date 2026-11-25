-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.cutSub_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:44:48.185809+00:00
-- url     : https://prove2.me/submissions/72136950-0088-4811-aaef-d12bbee5fc5d

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegQ
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegW

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
theorem _root_.solution (K : Type) [Field K] [NumberField K] (r : ℕ) : cutSub K r 0 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  funext i
  exact hx i (Nat.zero_le _)
end ReciprocityTheory.MultiplicativeHeights.SemiPt
