-- Prove2me | solution 1 for UpperTheory.prod_neg_one_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:58:51.632129+00:00
-- url     : https://prove2.me/submissions/941e8fa8-ee5e-4aff-aea8-390fd2007429

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow

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
namespace UpperTheory
theorem _root_.solution (e : ι → ℤ) : ∏ i, (-1 : K) ^ e i = (-1) ^ (∑ i, e i) := by
  classical
  refine Finset.induction_on (motive := fun s => ∏ i ∈ s, (-1 : K) ^ e i = (-1) ^ (∑ i ∈ s, e i)) Finset.univ (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ (by norm_num)]
end UpperTheory
