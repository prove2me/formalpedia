-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isJacobsonRing_int_223cc283b912
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:42:32.2908+00:00
-- url     : https://prove2.me/submissions/8ba25c44-f79a-4592-940f-7be5342b9bf1

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IntDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IntDimBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Algebra Cardinal
open scoped TensorProduct
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hb : P = ⊥
  · subst hb
    refine le_antisymm (fun n hn => ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_bot] at hn
    have h := hn n
    rw [Int.isUnit_iff] at h
    rw [Ideal.mem_bot]
    rcases h with h | h
    · exact mul_self_eq_zero.mp (by linarith)
    · nlinarith [mul_self_nonneg n]
  · haveI := hP
    haveI : P.IsMaximal := IsPrime.to_maximal_ideal hb
    exact Ideal.jacobson_eq_self_of_isMaximal
end GroundTheory.Heights₂.Heights
