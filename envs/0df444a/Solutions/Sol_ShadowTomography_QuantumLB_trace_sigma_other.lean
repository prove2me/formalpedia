-- Prove2me | solution 1 for ShadowTomography.QuantumLB.trace_sigma_other
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:14:44.436509+00:00
-- url     : https://prove2.me/submissions/45666a11-ec47-4ac8-82f7-3d70c7dae6ac

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_IsHalfProjector
import Definitions.Def_ShadowTomography_QuantumLB_rhoState
import Definitions.Def_ShadowTomography_QuantumLB_sigmaState

open ShadowTomography.QuantumLB in
theorem bb103639_key {N K : ℕ} (hN : 1 ≤ N) (P : Fin K → Matrix (Fin N) (Fin N) ℂ)
    (hP : ∀ i, IsHalfProjector (P i)) (ε : ℝ) (i j : Fin K) :
    (P j * sigmaState (P i) ε).trace.re - 1 / 2
      = 6 * ε * ((P j * rhoState (P i)).trace.re - 1 / 2) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have htr : (P j * sigmaState (P i) ε).trace
      = (((1 - 6 * ε) / 2 : ℝ) : ℂ) + ((6 * ε : ℝ) : ℂ) * (P j * rhoState (P i)).trace := by
    unfold sigmaState
    rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.trace_smul, Matrix.trace_smul, Matrix.mul_smul, Matrix.trace_smul, (hP j).2.2]
    simp only [smul_eq_mul]
    push_cast
    field_simp
  rw [htr, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  ring

open ShadowTomography.QuantumLB in
theorem solution {N K : ℕ} (hN : 1 ≤ N) (P : Fin K → Matrix (Fin N) (Fin N) ℂ)
    (hP : ∀ i, IsHalfProjector (P i))
    (h2 : ∀ i j, i ≠ j → |(P i * rhoState (P j)).trace.re - 1 / 2| ≤ 1 / 12)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ i j, i ≠ j →
      |(P j * sigmaState (P i) ε).trace.re - 1 / 2|
          = 6 * ε * |(P j * rhoState (P i)).trace.re - 1 / 2| ∧
        |(P j * sigmaState (P i) ε).trace.re - 1 / 2| ≤ ε / 2 := by
  intro i j hij
  have hk := bb103639_key hN P hP ε i j
  have heq : |(P j * sigmaState (P i) ε).trace.re - 1 / 2|
      = 6 * ε * |(P j * rhoState (P i)).trace.re - 1 / 2| := by
    rw [hk, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 6 * ε)]
  refine ⟨heq, ?_⟩
  rw [heq]
  have hb := h2 j i (Ne.symm hij)
  nlinarith
