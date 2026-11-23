-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qk20.kap_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:12.111077+00:00
-- url     : https://prove2.me/submissions/c3a09507-07cb-46ab-b567-0f91d2fbe3cb

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Qk20.cayley_transform_preserves_form {n : Type} [Fintype n] [DecidableEq n]
    (H Y : Matrix n n ℂ) (h : Y.conjTranspose * H + H * Y = 0) (hu : IsUnit (1 - Y).det) :
    ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹) = H := by
  have key : (1 + Y).conjTranspose * H * (1 + Y) = (1 - Y).conjTranspose * H * (1 - Y) := by
    have h' : Y.conjTranspose * H = -(H * Y) := eq_neg_of_add_eq_zero_left h
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      add_mul, sub_mul, one_mul, h']
    noncomm_ring
  have hinv : (1 - Y) * (1 - Y)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  calc ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹)
      = ((1 - Y)⁻¹).conjTranspose * ((1 + Y).conjTranspose * H * (1 + Y)) * (1 - Y)⁻¹ := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = ((1 - Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 - Y) * (1 - Y)⁻¹) := by
        rw [key, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = H := by rw [hinv, Matrix.conjTranspose_one, one_mul, mul_one]
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk20
theorem _root_.solution :
    ∀ {k r : ℕ} {Y : UpperTheory.Reformulated.B.Qk20.Mat k r},
      UpperTheory.Reformulated.B.Qk20.inLie k r Y →
        IsUnit (Matrix.det ((1 : UpperTheory.Reformulated.B.Qk20.Mat k r) - Y)) → UpperTheory.Reformulated.B.Qk20.kap Y ∈ UpperTheory.Reformulated.B.Qk20.GV k r := by
  intro k r Y h hu
  exact UpperTheory.Reformulated.B.Qk20.cayley_transform_preserves_form (UpperTheory.Reformulated.B.Qk20.Hpk k r) Y h hu
end UpperTheory.Reformulated.B.Qk20
