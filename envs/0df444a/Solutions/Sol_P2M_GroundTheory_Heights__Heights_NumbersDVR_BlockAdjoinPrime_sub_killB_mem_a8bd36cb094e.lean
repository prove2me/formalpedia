-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_sub_killB_mem_a8bd36cb094e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:11.226722+00:00
-- url     : https://prove2.me/submissions/af5488ea-6686-472e-bb2f-237066c3f371

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlockAdjoinPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_X_of_mem_f7bd28ee701b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_X_of_not_mem_1f46edb8b2e2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
variable {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
theorem _root_.solution (B : Set K) (p : MRing ι R) : p - killB B p ∈ varIdeal (R := R) B := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact add_mem hp hq
  | mul_X p v hp =>
    have e : p * X v - killB B (p * X v) =
        (p - killB B p) * X v + killB B p * (X v - killB B (X v)) := by
      rw [map_mul]; ring
    rw [e]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    by_cases hv : v.1 ∈ B
    · rw [killB_X_of_mem B hv, sub_zero]
      exact Ideal.subset_span ⟨v, hv, rfl⟩
    · rw [killB_X_of_not_mem B hv, sub_self]
      exact zero_mem _
end GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
