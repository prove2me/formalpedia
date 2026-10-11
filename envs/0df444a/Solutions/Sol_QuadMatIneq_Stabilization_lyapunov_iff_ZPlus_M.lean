-- Prove2me | solution 1 for QuadMatIneq.Stabilization.lyapunov_iff_ZPlus_M
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T18:12:39.359979+00:00
-- url     : https://prove2.me/submissions/d6658336-1e80-4c79-8cb7-e548f8f16ec5

import Definitions.Def_QuadMatIneq_Stabilization_QMI
import Definitions.Def_QuadMatIneq_Stabilization_Data
open Matrix QuadMatIneq.Stabilization
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

theorem solution {n m : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) (K : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    (P - (A + B * K) * P * (A + B * K)ᵀ).PosDef ↔
      Matrix.fromRows Aᵀ Bᵀ ∈ ZPlus (Mmat P K) := by
  have he : qmiForm (Mmat P K) (fromRows Aᵀ Bᵀ) =
      P - (A + B * K) * P * (A + B * K)ᵀ := by
    simp only [qmiForm, Mmat, transpose_fromRows, transpose_one, transpose_transpose,
      fromCols_mul_fromBlocks, fromCols_mul_fromRows, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    simp only [transpose_add, transpose_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    abel
  change _ ↔ (qmiForm (Mmat P K) (fromRows Aᵀ Bᵀ)).PosDef
  rw [he]
