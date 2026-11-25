-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.cutSub_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:44:46.454178+00:00
-- url     : https://prove2.me/submissions/b0ec82df-b7a0-4afa-bfa6-f95147f07546

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
theorem _root_.solution (K : Type) [Field K] [NumberField K] (r : ℕ) : cutSub K r r = ⊤ := by
  rw [eq_top_iff]
  intro x _ i hi
  exact absurd i.isLt (by omega)
end ReciprocityTheory.MultiplicativeHeights.SemiPt
