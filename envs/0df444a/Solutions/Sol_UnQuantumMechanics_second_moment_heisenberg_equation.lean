-- Prove2me | solution 1 for UnQuantumMechanics.second_moment_heisenberg_equation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T03:59:13.606132+00:00
-- url     : https://prove2.me/submissions/03415e82-0117-4310-a4ce-0519cdba4241

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQM1320

open UnQuantumMechanics

lemma eta0_mul : eta0 * eta0 = -1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [eta0, Matrix.mul_apply, Fin.sum_univ_two]

lemma eta0_t : eta0ᵀ = -eta0 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [eta0]

lemma g_mul (n : ℕ) : gamma0 n * gamma0 n = -1 := by
  unfold gamma0
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, eta0_mul]
  rw [show ((-1 : Matrix (Fin 2) (Fin 2) ℝ)) = (-1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) by simp]
  rw [Matrix.kronecker_smul, Matrix.one_kronecker_one]
  simp

lemma g_t (n : ℕ) : (gamma0 n)ᵀ = -gamma0 n := by
  unfold gamma0
  rw [← Matrix.kroneckerMap_transpose, Matrix.transpose_one, eta0_t]
  rw [show ((-eta0 : Matrix (Fin 2) (Fin 2) ℝ)) = (-1 : ℝ) • eta0 by simp]
  rw [Matrix.kronecker_smul]
  simp

lemma key (n : ℕ) (H Sig : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (hH : IsHamiltonianMatrix n H) :
    (H * Sig + Sig * Hᵀ) * (gamma0 n)ᵀ = H * autocorr n Sig - autocorr n Sig * H := by
  obtain ⟨A, hA, rfl⟩ := hH
  unfold autocorr
  have hAt : Aᵀ = A := hA
  rw [Matrix.transpose_mul, hAt, g_t]
  have hG := g_mul n
  set G := gamma0 n
  have e1 : (G * A * Sig + Sig * (A * -G)) * -G = -(G * A * Sig * G) + Sig * A * (G * G) := by
    noncomm_ring
  have e2 : G * A * (Sig * -G) - Sig * -G * (G * A) = -(G * A * Sig * G) + Sig * (G * G) * A := by
    noncomm_ring
  rw [e1, e2, hG]
  simp

end UnQM1320

open Matrix UnQuantumMechanics in
theorem solution (n : ℕ) (H : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (hH : IsHamiltonianMatrix n H)
    (Sig : ℝ → Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (τ : ℝ)
    (hSig : ∀ i j, HasDerivAt (fun t => Sig t i j) ((H * Sig τ + Sig τ * Hᵀ) i j) τ) :
    ∀ i j, HasDerivAt (fun t => autocorr n (Sig t) i j)
      ((H * autocorr n (Sig τ) - autocorr n (Sig τ) * H) i j) τ := by
  intro i j
  rw [← UnQM1320.key n H (Sig τ) hH]
  have : (fun t => autocorr n (Sig t) i j) =
      fun t => ∑ k, Sig t i k * (gamma0 n)ᵀ k j := by
    funext t; simp [autocorr, Matrix.mul_apply]
  rw [this]
  simp only [Matrix.mul_apply (M := H * Sig τ + Sig τ * Hᵀ)]
  exact HasDerivAt.fun_sum (fun k _ => (hSig i k).mul_const _)
