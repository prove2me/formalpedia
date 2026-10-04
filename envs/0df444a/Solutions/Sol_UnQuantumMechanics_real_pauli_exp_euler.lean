-- Prove2me | solution 1 for UnQuantumMechanics.real_pauli_exp_euler
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T07:34:37.808988+00:00
-- url     : https://prove2.me/submissions/ae71ac40-d4a3-4d81-bf7a-f9dc604341a8

import Mathlib
import Definitions.Def_UnQM_phase_space

set_option autoImplicit false

namespace E6455c69Aux

open Nat

theorem pow_even (η : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) (h : η * η = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (n : ℕ) : η ^ (2 * n) = c ^ n • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [pow_mul, sq, h, smul_pow, one_pow]

theorem pow_odd (η : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) (h : η * η = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (n : ℕ) : η ^ (2 * n + 1) = c ^ n • η := by
  rw [pow_succ, pow_even η c h, smul_one_mul]

theorem key (η : Matrix (Fin 2) (Fin 2) ℝ) (t c C S : ℝ)
    (h : η * η = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hC : HasSum (fun n : ℕ => c ^ n * t ^ (2 * n) / ↑(2 * n)!) C)
    (hS : HasSum (fun n : ℕ => c ^ n * t ^ (2 * n + 1) / ↑(2 * n + 1)!) S) :
    NormedSpace.exp (t • η) = C • (1 : Matrix (Fin 2) (Fin 2) ℝ) + S • η := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  refine HasSum.tsum_eq ?_
  refine HasSum.even_add_odd ?_ ?_
  · have e : ∀ n : ℕ, (c ^ n * t ^ (2 * n) / ↑(2 * n)! : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
        ((↑(2 * n)! : ℝ)⁻¹) • (t • η) ^ (2 * n) := by
      intro n
      rw [smul_pow, pow_even η c h, smul_smul, smul_smul]
      congr 1
      ring
    simpa only [e] using hC.smul_const (1 : Matrix (Fin 2) (Fin 2) ℝ)
  · have e : ∀ n : ℕ, (c ^ n * t ^ (2 * n + 1) / ↑(2 * n + 1)! : ℝ) • η =
        ((↑(2 * n + 1)! : ℝ)⁻¹) • (t • η) ^ (2 * n + 1) := by
      intro n
      rw [smul_pow, pow_odd η c h, smul_smul, smul_smul]
      congr 1
      ring
    simpa only [e] using hS.smul_const η

end E6455c69Aux

open Matrix UnQuantumMechanics in
theorem solution (η : Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ) :
    (η * η = -1 → NormedSpace.exp (φ • η) = Real.cos φ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sin φ • η) ∧
    (η * η = 1 → NormedSpace.exp (φ • η) = Real.cosh φ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sinh φ • η) := by
  constructor
  · intro h
    have h' : η * η = (-1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [h, neg_smul, one_smul]
    exact E6455c69Aux.key η φ (-1) _ _ h' (Real.hasSum_cos φ) (Real.hasSum_sin φ)
  · intro h
    have h' : η * η = (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [h, one_smul]
    exact E6455c69Aux.key η φ 1 _ _ h' (by simpa using Real.hasSum_cosh φ)
      (by simpa using Real.hasSum_sinh φ)
