-- Prove2me | solution 1 for STVFriedmann.eigenvalues_SM_every_order
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T08:17:44.104399+00:00
-- url     : https://prove2.me/submissions/07fedc0b-04be-4393-a0aa-88dfc75fe4cb

import Mathlib
import Definitions.Def_STVFriedmann_basic
open Filter Topology Real STVFriedmann

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    (stvBlockP k restSM1).charpoly =
      (Polynomial.X - Polynomial.C (2 * (k : ℝ) / 3)) *
        (Polynomial.X - Polynomial.C ((2 * (k : ℝ) - 5) / 3)) := by
  rw [Matrix.charpoly_fin_two]
  have h2k : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have htr : (stvBlockP k restSM1).trace = (4 * (k:ℝ) - 5) / 3 := by
    simp [stvBlockP, restSM1, Matrix.trace_fin_two]; ring
  have hdet : (stvBlockP k restSM1).det = 2 * (k:ℝ) * (2 * k - 5) / 9 := by
    simp [stvBlockP, restSM1, Matrix.det_fin_two]; field_simp; ring
  rw [htr, hdet]
  have e1 : Polynomial.C ((4 * (k:ℝ) - 5) / 3)
      = Polynomial.C (2 * (k : ℝ) / 3) + Polynomial.C ((2 * (k : ℝ) - 5) / 3) := by
    rw [← Polynomial.C_add]; congr 1; ring
  have e2 : Polynomial.C (2 * (k:ℝ) * (2 * k - 5) / 9)
      = Polynomial.C (2 * (k : ℝ) / 3) * Polynomial.C ((2 * (k : ℝ) - 5) / 3) := by
    rw [← Polynomial.C_mul]; congr 1; ring
  rw [e1, e2]
  ring
