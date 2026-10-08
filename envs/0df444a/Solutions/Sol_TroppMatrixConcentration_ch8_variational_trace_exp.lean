-- Prove2me | solution 1 for TroppMatrixConcentration.ch8_variational_trace_exp
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:44:33.672341+00:00
-- url     : https://prove2.me/submissions/cb69bf5c-e8a1-4ac3-a987-1a1f59f81f3f

import Theorems.Thm_TroppMatrixConcentration_ch8_variational_trace
import Theorems.Thm_TroppMatrixConcentration_ch3_cgf_exp_log
import Mathlib.Tactic.Ring

open scoped Matrix.Norms.L2Operator ComplexOrder
open TroppMatrixConcentration
set_option autoImplicit false

theorem solution {d : ℕ} [NeZero d]
    (H A : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) (hA : A.PosDef) :
    IsGreatest {r : ℝ | ∃ T : Matrix (Fin d) (Fin d) ℂ,
      T.PosDef ∧ r = (Matrix.trace (T * H)).re + (Matrix.trace A).re -
        ch8_relativeEntropy T A}
      (traceExp (H + matrixLog A)) := by
  have hHerm : (H + matrixLog A).IsHermitian := hH.add (cfc_predicate Real.log A)
  obtain ⟨hPD, hLog⟩ := ch3_cgf_exp_log (H + matrixLog A) hHerm
  have hVar := ch8_variational_trace (matrixExp (H + matrixLog A)) hPD
  have score (T : Matrix (Fin d) (Fin d) ℂ) :
      (Matrix.trace (T * matrixLog (matrixExp (H + matrixLog A)) - T * matrixLog T + T)).re =
        (Matrix.trace (T * H)).re + (Matrix.trace A).re - ch8_relativeEntropy T A := by
    rw [hLog]
    simp only [ch8_relativeEntropy, mul_add, mul_sub, Matrix.trace_add, Matrix.trace_sub,
      Complex.add_re, Complex.sub_re]
    ring
  constructor
  · obtain ⟨T,hT,hEq⟩ := hVar.1
    exact ⟨T,hT,hEq.trans (score T)⟩
  · rintro r ⟨T,hT,rfl⟩
    rw [← score T]
    exact hVar.2 ⟨T,hT,rfl⟩
