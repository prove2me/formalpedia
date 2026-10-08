-- Prove2me | solution 1 for RhinViola.final_polynomials_covariant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T21:28:38.439971+00:00
-- url     : https://prove2.me/submissions/910198eb-e470-4b0d-bfb8-cf697d07b10f

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

theorem solution
    (x y : ℂ) (hxy : 1 - x * y ≠ 0) :
    (let Q : ℂ → ℂ → ℂ := fun u v =>
        (2 * u - 1) * (2 * v - 1) * (2 * u * v - 1) *
          (1 - 2 * u + u * v) * (1 - 2 * v + u * v);
     let R : ℂ → ℂ → ℂ := fun u v =>
        ((u - v) * (1 - 2 * u + u ^ 2 * v) *
          (1 - 2 * v + u * v ^ 2) * (1 - u - u * v) *
          (1 - v - u * v)) ^ 2;
     let S : ℂ → ℂ → ℂ := fun u v =>
        (3 * u - 2) * (3 * v - 2) * (3 * u * v - 1) *
          (1 - 3 * u + 2 * u * v) * (1 - 3 * v + 2 * u * v);
     let ξ : ℂ := (1 - x) / (1 - x * y);
     let η : ℂ := 1 - x * y;
     (η ^ 2 * Q ξ η = x ^ 2 * Q x y) ∧
       (η ^ 6 * R ξ η = x ^ 6 * R x y) ∧
       (η ^ 2 * S ξ η = x ^ 2 * S x y)) := by
  dsimp
  constructor
  · field_simp [hxy] <;> ring
  constructor
  · field_simp [hxy] <;> ring
  · field_simp [hxy] <;> ring
