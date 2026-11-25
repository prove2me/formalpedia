-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.wa_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:06:15.777655+00:00
-- url     : https://prove2.me/submissions/0bcdb5cc-1c6a-45b0-974b-9d11e2225ea4

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_symm
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_sum_right

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r n : ℕ} (S : HermForm K r)
    (y : Fin r → K) (t : Fin n → K) (b : Fin n → Fin r → K) :
    S.h (∑ i, t i • b i) y = ∑ i, S.c (t i) * S.h (b i) y := by
  rw [wa_symm S y, wa_sum_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← wa_symm S y (b i)]
end ReciprocityTheory.MultiplicativeHeights
