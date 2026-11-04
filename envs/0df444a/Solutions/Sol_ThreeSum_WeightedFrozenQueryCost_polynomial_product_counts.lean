-- Prove2me | solution 1 for ThreeSum.WeightedFrozenQueryCost.polynomial_product_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:15:01.682507+00:00
-- url     : https://prove2.me/submissions/c1a3cd8c-e74e-4d3b-a5ca-e3c4ba49713a

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenQueryCost

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration
namespace ThreeSum.WeightedFrozenQueryCost
theorem _root_.solution {N : ℕ} (Q : Word N) (z : ℝ) :
    (∏ i : Fin N, (if Q i=0 then 1 else if Q i=1 then 1+z^512 else 1+z^513+z^1025)) =
      (1+z^512)^TernaryJointType.digitCount Q 1 *
        (1+z^513+z^1025)^TernaryJointType.digitCount Q 2 := by
  have hl (q : Fin 3) :
      (if q=0 then 1 else if q=1 then 1+z^512 else 1+z^513+z^1025) =
        (1+z^512)^(if q=1 then 1 else 0 : ℕ) *
          (1+z^513+z^1025)^(if q=2 then 1 else 0 : ℕ) := by
    fin_cases q <;> norm_num [Fin.ext_iff]
  simp_rw [hl]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Finset.prod_pow_eq_pow_sum]
  rfl
end ThreeSum.WeightedFrozenQueryCost
