-- Prove2me | solution 1 for QuantumParallelRepetition.positive_complement_quadraticExpectation_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/b4f81f08-3f53-458c-b1cc-c6103a7bf0ef

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace QuantumParallelRepetition
theorem _root_.solution
    (W : H →L[ℂ] H)
    (h_complement : (1 - W).IsPositive) (z : H) :
    quadraticExpectation W z ≤ ‖z‖ ^ 2 := by
  have h := h_complement.re_inner_nonneg_right z
  have hnorm : (⟪z, z⟫_ℂ).re = ‖z‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp [pow_two, Complex.mul_re]
  change 0 ≤ (⟪z, z - W z⟫_ℂ).re at h
  rw [inner_sub_right, Complex.sub_re, hnorm] at h
  unfold quadraticExpectation
  exact sub_nonneg.mp h
end QuantumParallelRepetition
