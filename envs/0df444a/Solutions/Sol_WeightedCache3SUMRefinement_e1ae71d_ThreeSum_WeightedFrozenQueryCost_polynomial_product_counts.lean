-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost.polynomial_product_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:09:33.968205+00:00
-- url     : https://prove2.me/submissions/a2c919de-e3d8-48cd-a1c0-02f7e1b7e48c

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost
theorem _root_.solution {N : ℕ} (Q : Word N) (z : ℝ) :
    (∏ i : Fin N, (if Q i=0 then 1 else if Q i=1 then 1+z^1369 else 1+z^1371+z^2740)) =
      (1+z^1369)^TernaryJointType.digitCount Q 1 *
        (1+z^1371+z^2740)^TernaryJointType.digitCount Q 2 := by
  have hl (q : Fin 3) :
      (if q=0 then 1 else if q=1 then 1+z^1369 else 1+z^1371+z^2740) =
        (1+z^1369)^(if q=1 then 1 else 0 : ℕ) *
          (1+z^1371+z^2740)^(if q=2 then 1 else 0 : ℕ) := by
    fin_cases q <;> norm_num [Fin.ext_iff]
  simp_rw [hl]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Finset.prod_pow_eq_pow_sum]
  rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrozenQueryCost
