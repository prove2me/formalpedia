-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.wa_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:06:12.326228+00:00
-- url     : https://prove2.me/submissions/d4801fa5-0a8f-466e-b473-be6490d08e1f

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
    (x y z : Fin r → K) : S.h (x - y) z = S.h x z - S.h y z := by
  simp only [HermForm.h, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
end ReciprocityTheory.MultiplicativeHeights
