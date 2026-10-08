-- Prove2me | solution 1 for ShadowTomography.QuantumLB.trace_sigma_self
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T13:24:40.24319+00:00
-- url     : https://prove2.me/submissions/c974d6b7-7744-46e4-a36d-5f08aec52b52

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_IsHalfProjector
import Definitions.Def_ShadowTomography_QuantumLB_sigmaState

open ShadowTomography.QuantumLB in
theorem solution {N : ℕ} (hN : 1 ≤ N) (P : Matrix (Fin N) (Fin N) ℂ)
    (hP : IsHalfProjector P) (ε : ℝ) :
    (P * sigmaState P ε).trace.re = 1 / 2 + 3 * ε := by
  obtain ⟨_, hPP, htr⟩ := hP
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have key : (P * sigmaState P ε).trace = ((1 / 2 + 3 * ε : ℝ) : ℂ) := by
    unfold sigmaState rhoState
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hPP, Matrix.trace_add,
      Matrix.trace_smul, htr, smul_eq_mul]
    push_cast
    field_simp
    ring
  rw [key, Complex.ofReal_re]
