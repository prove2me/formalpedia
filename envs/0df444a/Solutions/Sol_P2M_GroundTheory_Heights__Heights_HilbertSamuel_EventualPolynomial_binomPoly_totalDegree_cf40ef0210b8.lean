-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_binomPoly_totalDegree_cf40ef0210b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:40.412855+00:00
-- url     : https://prove2.me/submissions/75a89e36-c908-4b3a-b1a1-75a3ee2dfdd7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolynomial

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Finset fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
variable {K : Type} [DecidableEq K]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
theorem _root_.solution (c : ℕ) (k : K) (j : ℕ) : (binomPoly c k j).totalDegree ≤ j := by
  unfold binomPoly
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ range j, (X k - C ((c + i : ℕ) : ℚ) : MvPolynomial K ℚ).totalDegree
        ≤ ∑ _i ∈ range j, 1 :=
          sum_le_sum fun i _ => (totalDegree_sub_C_le _ _).trans (by rw [totalDegree_X])
    _ = j := by simp
end GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
