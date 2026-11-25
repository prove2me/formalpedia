-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.wa_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:27:21.328624+00:00
-- url     : https://prove2.me/submissions/ccde1f6a-bb61-4077-a0f0-ae65062841a6

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA

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
open Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x : Fin r → K) : S.h x 0 = 0 := by
  simp [HermForm.h]
end ReciprocityTheory.MultiplicativeHeights
