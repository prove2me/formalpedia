-- Prove2me | solution 1 for SiegelFields.sq_eq_trace_smul_sub_det
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T16:52:19.225037+00:00
-- url     : https://prove2.me/submissions/8022aec8-c344-4ac2-b2a7-7c2c29b9695c

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex SiegelFields

theorem solution :
    (∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      M * M = trace M • M - M.det • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (∀ V : Matrix (Fin 2) (Fin 2) ℂ, IsThreeVector V →
      V * V = (-V.det) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      V * V = ((1 / 2 : ℂ) * trace (V * V)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hCH : ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      M * M = trace M • M - M.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, trace_fin_two, det_fin_two, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.sub_apply, one_apply] <;>
      ring
  refine ⟨hCH, ?_⟩
  intro V hV
  have htr : trace V = 0 := hV.2
  have hsq : V * V = -V.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simpa [htr, zero_smul, zero_sub, neg_smul] using hCH V
  have htrace : trace (V * V) = -2 * V.det := by
    have hId : trace (V * V) - (trace V) ^ 2 = -2 * V.det := by
      simp only [det_fin_two, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have h := hId
    rw [htr] at h
    simp at h
    calc
      trace (V * V) = -(2 * V.det) := h
      _ = -2 * V.det := by ring
  constructor
  · exact hsq
  · calc
      V * V = -V.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := hsq
      _ = ((1 / 2 : ℂ) * trace (V * V)) • 1 := by
        congr 1
        rw [htrace]
        ring
