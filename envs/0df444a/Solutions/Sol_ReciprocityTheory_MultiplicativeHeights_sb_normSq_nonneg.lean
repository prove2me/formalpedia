-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_normSq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:59:56.055874+00:00
-- url     : https://prove2.me/submissions/2393f9a5-a21e-4b73-a77e-9ba70f19c99f

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
theorem _root_.solution {r : ℕ} (v : Fin r → ℂ) : 0 ≤ normSq v :=
  Finset.sum_nonneg fun _ _ => by positivity
end ReciprocityTheory.MultiplicativeHeights
