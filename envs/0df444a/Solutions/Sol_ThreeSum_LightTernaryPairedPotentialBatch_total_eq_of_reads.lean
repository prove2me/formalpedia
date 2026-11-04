-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPotentialBatch.total_eq_of_reads
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:35:55.551662+00:00
-- url     : https://prove2.me/submissions/abc5fda7-d8ac-4877-a155-ab7c9e561d7b

import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatch
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatchFinal
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_tensorIndex_lt
import Theorems.Thm_ThreeSum_WeightEnumeration_digit_lt


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPairedPotentialBatch
open Light
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPotentialBatch
theorem _root_.solution (K base Λ H : ℕ) (μ ν : ℕ→ℤ) (hΛ : 1≤Λ)
    (hread : ∀ i<H, ∀ q<Λ^4, μ (base+i*Λ^4+q)=ν (base+i*Λ^4+q)) :
    total K base Λ μ H=total K base Λ ν H := by
  unfold total
  apply Finset.sum_congr rfl
  intro i hi
  unfold term LightTernaryPairedPotential.prefixSum
  apply Finset.sum_congr rfl
  intro j hj
  unfold LightTernaryPairedPotential.term
  congr 1
  funext q
  exact hread i (Finset.mem_range.mp hi) _ (LightTernaryPairedPolynomial.tensorIndex_lt
    (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega))
    (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega)))
end ThreeSum.LightTernaryPairedPotentialBatch
