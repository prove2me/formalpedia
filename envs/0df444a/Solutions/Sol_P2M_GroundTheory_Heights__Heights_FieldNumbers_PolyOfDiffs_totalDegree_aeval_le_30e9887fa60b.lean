-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_totalDegree_aeval_le_30e9887fa60b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:52.035925+00:00
-- url     : https://prove2.me/submissions/dc035fa8-8fd1-43e9-a3e3-dc9ac9827cb5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
open GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
theorem _root_.solution (g : K → MvPolynomial K ℚ) (hg : ∀ j, (g j).totalDegree ≤ 1)
    (P : MvPolynomial K ℚ) : (aeval g P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun α hα => ?_
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  unfold Finsupp.prod
  refine (totalDegree_finsetProd _ _).trans
    ((Finset.sum_le_sum fun j _ => ?_).trans (le_totalDegree hα))
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (α j) (hg j))
end GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
