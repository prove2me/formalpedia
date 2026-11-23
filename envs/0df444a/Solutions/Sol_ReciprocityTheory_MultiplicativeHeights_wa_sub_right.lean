-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.wa_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:51.738807+00:00
-- url     : https://prove2.me/submissions/de313f84-6d0c-4724-bb97-1b53cf5ffd3e

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
    (x y z : Fin r → K) : S.h x (y - z) = S.h x y - S.h x z := by
  simp only [HermForm.h, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
end ReciprocityTheory.MultiplicativeHeights
