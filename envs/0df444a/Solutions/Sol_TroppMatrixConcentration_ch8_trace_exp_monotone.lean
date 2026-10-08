-- Prove2me | solution 1 for TroppMatrixConcentration.ch8_trace_exp_monotone
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:44:29.61047+00:00
-- url     : https://prove2.me/submissions/c8e3a873-b8ea-47df-95f2-b37051a5f774

import Theorems.Thm_TroppMatrixConcentration_ch8_entropy_nonnegative
import Theorems.Thm_TroppMatrixConcentration_ch3_cgf_exp_log
import Mathlib.Tactic.Linarith
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix
private theorem trace_mul_nonneg {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  let S := CFC.sqrt A
  have hS : Sᴴ = S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hp := (hB.mul_mul_conjTranspose_same S).trace_nonneg
  have ht : Matrix.trace (S * B * Sᴴ) = Matrix.trace (A * B) := by
    rw [hS, Matrix.trace_mul_cycle, hSS]
  rw [ht] at hp
  exact (RCLike.nonneg_iff.mp hp).1

open TroppMatrixConcentration
set_option autoImplicit false

theorem solution {d : ℕ} [NeZero d]
    (A H : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hAH : loewnerLE A H) :
    traceExp A ≤ traceExp H := by
  obtain ⟨hEA, hLA⟩ := ch3_cgf_exp_log A hA
  obtain ⟨hEH, hLH⟩ := ch3_cgf_exp_log H hH
  have he := ch8_entropy_nonnegative (matrixExp A) (matrixExp H) hEA hEH
  have hp := trace_mul_nonneg (matrixExp A) (H - A) hEA.posSemidef hAH
  simp only [ch8_relativeEntropy, hLA, hLH, mul_sub, Matrix.trace_sub,
    Complex.sub_re] at he hp
  unfold traceExp
  linarith
