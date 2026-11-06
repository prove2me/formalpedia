-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.algEquivRingHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:18:16.264188+00:00
-- url     : https://prove2.me/submissions/277bc275-a182-4b4f-862e-6671fa0b8c02

import Mathlib.AlgebraicGeometry.Pullbacks
set_option autoImplicit false
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

theorem solution (e : A ≃ₐ[R] B) (x : A) : e.toRingHom x = e x := by
  rfl
