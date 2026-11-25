-- Prove2me | solution 1 for UpperTheory.MU.even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:10:41.556456+00:00
-- url     : https://prove2.me/submissions/d20c8ebc-693e-4d16-a847-6412b636a4eb

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Theorems.Thm_UpperTheory_prod_neg_one_zpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory
variable {E K K' : Type} [Field E] [Field K] [Field K'] {ι ι' : Type} [Fintype ι] [Fintype ι']
open UpperTheory.MU
variable {φ : ι → E →+* K} {e e' : ι → ℤ}
namespace UpperTheory.MU
theorem _root_.solution [CharZero K] (h : MU φ e) : Even (∑ i, e i) := by
  have h1 := h (-1) ⟨2, by norm_num, by norm_num⟩
  simp only [map_neg, map_one] at h1
  rw [prod_neg_one_zpow] at h1
  by_contra hodd
  rw [Int.not_even_iff_odd] at hodd
  rw [hodd.neg_one_zpow] at h1
  norm_num at h1
end UpperTheory.MU
