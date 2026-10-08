-- Prove2me | solution 1 for TroppMatrixConcentration.ch8_variational_trace
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:44:32.620795+00:00
-- url     : https://prove2.me/submissions/698f9be4-40cb-4c28-90eb-5515c8856d5c

import Theorems.Thm_TroppMatrixConcentration_ch8_entropy_nonnegative
import Mathlib.Tactic.Linarith

open scoped Matrix.Norms.L2Operator ComplexOrder
open TroppMatrixConcentration
set_option autoImplicit false

theorem solution {d : ℕ} [NeZero d]
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosDef) :
    IsGreatest {r : ℝ | ∃ T : Matrix (Fin d) (Fin d) ℂ,
      T.PosDef ∧ r = (Matrix.trace (T * matrixLog M - T * matrixLog T + T)).re}
      (Matrix.trace M).re := by
  constructor
  · exact ⟨M, hM, by simp⟩
  · rintro r ⟨T, hT, rfl⟩
    have h := ch8_entropy_nonnegative T M hT hM
    simp only [ch8_relativeEntropy, mul_sub, Matrix.trace_sub, Complex.sub_re] at h
    simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re]
    linarith
