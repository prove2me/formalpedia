-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_isJacobsonRing_int_5cab28bc29cb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:41.218138+00:00
-- url     : https://prove2.me/submissions/fd7ec6d7-31e0-49db-b4e3-f555645285dd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped nonZeroDivisors
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h0 : P = ⊥
  · subst h0
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_iff] at hx
    obtain ⟨z₁, hz₁⟩ := hx 1
    obtain ⟨z₂, hz₂⟩ := hx 2
    rw [Ideal.mem_bot] at hz₁ hz₂ ⊢
    have e1 : (x + 1) * z₁ = 1 := by linear_combination hz₁
    have e2 : (2 * x + 1) * z₂ = 1 := by linear_combination hz₂
    have h1 : IsUnit (x + 1) := ⟨⟨x + 1, z₁, e1, (mul_comm _ _).trans e1⟩, rfl⟩
    have h2 : IsUnit (2 * x + 1) := ⟨⟨2 * x + 1, z₂, e2, (mul_comm _ _).trans e2⟩, rfl⟩
    rw [Int.isUnit_iff] at h1 h2
    omega
  · have : P.IsMaximal := IsPrime.to_maximal_ideal h0
    exact Ideal.jacobson_eq_self_of_isMaximal
end GroundTheory.Heights₂.Heights.Model
