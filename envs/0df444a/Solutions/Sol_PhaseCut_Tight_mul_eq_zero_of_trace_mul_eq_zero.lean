-- Prove2me | solution 1 for PhaseCut.Tight.mul_eq_zero_of_trace_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:16:53.745298+00:00
-- url     : https://prove2.me/submissions/374b3595-0097-4fdf-bc51-e3d0da7841b4

import Mathlib
import Definitions.Def_PhaseCut_Tight_Defs
set_option autoImplicit false
open Matrix PhaseCut.Tight
open scoped ComplexOrder MatrixOrder

theorem solution {m : ℕ} (U M : Matrix (Fin m) (Fin m) ℂ)
    (hU : U.PosSemidef) (hM : M.PosSemidef) (h : (U * M).trace = 0) :
    U * M = 0 := by
  obtain ⟨W, hW⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hU.nonneg
  obtain ⟨N, hN⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  have hW' : U = Wᴴ * W := hW
  have hN' : M = Nᴴ * N := hN
  have h1 : ((W * Nᴴ) * (W * Nᴴ)ᴴ).trace = 0 := by
    have : ((W * Nᴴ) * (W * Nᴴ)ᴴ).trace = (U * M).trace := by
      rw [hW', hN', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [Matrix.trace_mul_comm (Wᴴ * W)]
      simp only [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [this, h]
  have h2 : W * Nᴴ = 0 := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.1 h1
  rw [hW', hN']
  calc Wᴴ * W * (Nᴴ * N) = Wᴴ * (W * Nᴴ) * N := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h2]; simp
