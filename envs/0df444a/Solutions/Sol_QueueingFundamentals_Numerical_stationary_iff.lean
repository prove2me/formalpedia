-- Prove2me | solution 1 for QueueingFundamentals.Numerical.stationary_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:18:10.316568+00:00
-- url     : https://prove2.me/submissions/e3169b5a-9935-4c8a-9a8e-841336d75693

import Mathlib
import Definitions.Def_QueueingFundamentals_Numerical_Uniformization

open Matrix

open Matrix QueueingFundamentals.Numerical in
theorem solution {N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (Λ : ℝ) (hΛ : 0 < Λ) (φ : Fin (N + 1) → ℝ) :
    φ = φ ᵥ* uniformizedMatrix Λ Q ↔ φ ᵥ* Q = 0 := by
  have h : φ ᵥ* uniformizedMatrix Λ Q = Λ⁻¹ • (φ ᵥ* Q) + φ := by
    unfold uniformizedMatrix
    rw [Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_one]
  rw [h]
  have hinv : Λ⁻¹ ≠ 0 := inv_ne_zero hΛ.ne'
  constructor
  · intro e
    have e2 : Λ⁻¹ • (φ ᵥ* Q) = 0 := by
      have := congrArg (fun v => v - φ) e
      simpa using this.symm
    exact (smul_eq_zero.mp e2).resolve_left hinv
  · intro e
    rw [e, smul_zero, zero_add]
