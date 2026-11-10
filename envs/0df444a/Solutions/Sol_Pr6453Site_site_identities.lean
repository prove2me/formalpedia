-- Prove2me | solution 1 for Pr6453Site.site_identities
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-09T09:10:13.317297+00:00
-- url     : https://prove2.me/submissions/f2d56385-b231-4853-8ee8-ac84620c5455

import Mathlib

set_option autoImplicit false

namespace Pr6453Site

open Matrix

theorem conj_mul_conj {n : Type*} [Fintype n] [DecidableEq n]
    (c ci D E : Matrix n n ℚ) (h : ci * c = 1) :
    (c * D * ci) * (c * E * ci) = c * (D * E) * ci := by
  calc (c * D * ci) * (c * E * ci) = c * D * (ci * c) * E * ci := by noncomm_ring
    _ = c * D * 1 * E * ci := by rw [h]
    _ = c * (D * E) * ci := by noncomm_ring

end Pr6453Site


theorem solution {n : Type*} [Fintype n] [DecidableEq n]
    (c ci : Matrix n n ℚ) (h : ci * c = 1) :
    (∀ d : n → ℚ, (∀ i, d i * d i = d i) →
        (c * Matrix.diagonal d * ci) * (c * Matrix.diagonal d * ci)
          = c * Matrix.diagonal d * ci) ∧
      (∀ α β : Matrix n n ℚ, β * α = α →
        (c * β * ci) * (c * α * ci) = c * α * ci) ∧
      (∀ d e : n → ℚ, (∀ i, d i * e i = e i * d i) →
        (c * Matrix.diagonal d * ci) * (c * Matrix.diagonal e * ci)
          = (c * Matrix.diagonal e * ci) * (c * Matrix.diagonal d * ci)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rw [Pr6453Site.conj_mul_conj c ci _ _ h, Matrix.diagonal_mul_diagonal,
      show (fun i => d i * d i) = d from funext fun i => hd i]
  · intro α β hβα
    rw [Pr6453Site.conj_mul_conj c ci _ _ h, hβα]
  · intro d e hd
    have hde : Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
        show (fun i => d i * e i) = (fun i => e i * d i) from funext fun i => hd i]
    rw [Pr6453Site.conj_mul_conj c ci _ _ h, Pr6453Site.conj_mul_conj c ci _ _ h, hde]
