-- Prove2me | solution 1 for adjugate_symm_fin_four
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T17:35:16.823736+00:00
-- url     : https://prove2.me/submissions/cfc1d21b-ab99-45ac-a22f-6ea66f202f71

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option maxRecDepth 20000 in
theorem solution (a b c d e f h i j k : ℝ) :
    (!![a, b, c, d; b, e, f, h; c, f, i, j; d, h, j, k] : Matrix (Fin 4) (Fin 4) ℝ).adjugate =
      !![e*i*k - e*j^2 - f^2*k + 2*f*h*j - h^2*i, -b*i*k + b*j^2 + c*f*k - c*h*j - d*f*j + d*h*i,
          b*f*k - b*h*j - c*e*k + c*h^2 + d*e*j - d*f*h, -b*f*j + b*h*i + c*e*j - c*f*h - d*e*i + d*f^2;
        -b*i*k + b*j^2 + c*f*k - c*h*j - d*f*j + d*h*i, a*i*k - a*j^2 - c^2*k + 2*c*d*j - d^2*i,
          -a*f*k + a*h*j + b*c*k - b*d*j - c*d*h + d^2*f, a*f*j - a*h*i - b*c*j + b*d*i + c^2*h - c*d*f;
        b*f*k - b*h*j - c*e*k + c*h^2 + d*e*j - d*f*h, -a*f*k + a*h*j + b*c*k - b*d*j - c*d*h + d^2*f,
          a*e*k - a*h^2 - b^2*k + 2*b*d*h - d^2*e, -a*e*j + a*f*h + b^2*j - b*c*h - b*d*f + c*d*e;
        -b*f*j + b*h*i + c*e*j - c*f*h - d*e*i + d*f^2, a*f*j - a*h*i - b*c*j + b*d*i + c^2*h - c*d*f,
          -a*e*j + a*f*h + b^2*j - b*c*h - b*d*f + c*d*e, a*e*i - a*f^2 - b^2*i + 2*b*c*f - c^2*e] := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove] <;> ring
