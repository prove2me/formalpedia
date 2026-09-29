-- Prove2me | solution 1 for SiegelFields.threeVector_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T16:54:36.679986+00:00
-- url     : https://prove2.me/submissions/f8a36344-a1e8-4270-b34f-a9a987d4c3c6

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex SiegelFields ComplexConjugate

theorem solution (V : Matrix (Fin 2) (Fin 2) ℂ) (hV : IsThreeVector V) :
    -2 * V.det = trace (V * V) ∧ (trace (V * V)).im = 0 ∧ 0 ≤ (trace (V * V)).re ∧
      (trace (V * V) = 0 ↔ V = 0) := by
  have htr : trace V = 0 := hV.2
  have hH : V.IsHermitian := hV.1
  have hId : trace (V * V) - (trace V) ^ 2 = -2 * V.det := by
    simp only [det_fin_two, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hAlg : -2 * V.det = trace (V * V) := by
    have h := hId
    rw [htr] at h
    simp at h
    calc
      -2 * V.det = -(2 * V.det) := by ring
      _ = trace (V * V) := by
        simpa using h.symm
  have h01 : star (V 1 0) = V 0 1 := hH.apply 0 1
  have h11 : V 1 1 = -V 0 0 := by
    simp only [trace_fin_two] at htr
    linear_combination htr
  have hreal : V 0 0 = ((V 0 0).re : ℂ) :=
    (conj_eq_iff_re.mp (by simpa [star_def] using hH.apply 0 0)).symm
  set a : ℝ := (V 0 0).re
  set z : ℂ := V 1 0
  have hdet : V.det = -((a ^ 2 + normSq z : ℝ) : ℂ) := by
    simp only [det_fin_two, h11, hreal]
    rw [← h01, star_def, ← normSq_eq_conj_mul_self]
    push_cast
    ring
  have htrvv : trace (V * V) = ((2 * (a ^ 2 + normSq z) : ℝ) : ℂ) := by
    rw [← hAlg, hdet]
    push_cast
    ring
  refine ⟨hAlg, ?_, ?_, ?_⟩
  · rw [htrvv]
    exact ofReal_im _
  · rw [htrvv, ofReal_re]
    exact mul_nonneg (by norm_num) (add_nonneg (sq_nonneg a) (normSq_nonneg z))
  · constructor
    · intro h0
      have hsum : a ^ 2 + normSq z = 0 := by
        have hre := congrArg re h0
        rw [htrvv, ofReal_re, zero_re] at hre
        linarith
      have hz : normSq z = 0 := by nlinarith [sq_nonneg a, normSq_nonneg z]
      have ha : a = 0 := by nlinarith [sq_nonneg a, normSq_nonneg z]
      have hz0 : z = 0 := normSq_eq_zero.mp hz
      ext i j
      fin_cases i <;> fin_cases j <;> dsimp
      · simp [hreal, ha]
      · rw [← h01, hz0]
        simp
      · exact hz0
      · simp [h11, hreal, ha]
    · intro h0
      simp [h0]
