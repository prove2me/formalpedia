-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_prod_line_pow_7d765d194025
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:54:40.994582+00:00
-- url     : https://prove2.me/submissions/ec1298d2-e7d3-441e-9d52-9714b83d617b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolyLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolyLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial GroundTheory.Heights₂.Heights.NumbersDVR fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
theorem _root_.solution (a c : K → ℚ) (s : K → ℕ) (S : Finset K) :
    (∏ k ∈ S, (C (a k) * X + C (c k)) ^ (s k)).natDegree ≤ ∑ k ∈ S, s k ∧
      (∏ k ∈ S, (C (a k) * X + C (c k)) ^ (s k)).coeff (∑ k ∈ S, s k) = ∏ k ∈ S, a k ^ (s k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    have h1 : ((C (a k) * X + C (c k)) ^ (s k)).natDegree ≤ s k := by
      simpa using natDegree_pow_le_of_le (s k) (natDegree_linear_le (a := a k) (b := c k))
    have h2 : ((C (a k) * X + C (c k)) ^ (s k)).coeff (s k) = a k ^ s k := by
      have := coeff_pow_of_natDegree_le (m := s k) (natDegree_linear_le (a := a k) (b := c k))
      simpa using this
    rw [Finset.prod_insert hk, Finset.sum_insert hk, Finset.prod_insert hk]
    exact ⟨natDegree_mul_le.trans (add_le_add h1 ih.1),
      by rw [coeff_mul_add_eq_of_natDegree_le h1 ih.1, h2, ih.2]⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
