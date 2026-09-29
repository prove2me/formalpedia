-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.eval_eq_specialized_eval
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:53.602569+00:00
-- url     : https://prove2.me/submissions/72ba313e-a695-457e-8e23-e098be525f88

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (p : MvPolynomial (Fin 2) ℝ) (z : Point2) :
    MvPolynomial.eval (fun i => z i) p =
      Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) p) := by
  have hcons :
      Fin.cons (elimCoord z) (fun _ : Fin 1 => coeffCoord z) = fun i => z i := by
    ext i
    fin_cases i
    · simp [elimCoord, coeffCoord]
    · simp [elimCoord, coeffCoord]
  calc
    MvPolynomial.eval (fun i => z i) p =
        MvPolynomial.eval (Fin.cons (elimCoord z) (fun _ : Fin 1 => coeffCoord z)) p := by
      rw [hcons]
    _ = Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) p) := by
      simpa [Specialized0, coeffEval, elimCoord, coeffCoord, Curry0]
        using (MvPolynomial.eval_eq_eval_mv_eval'
          (s := fun _ : Fin 1 => coeffCoord z) (y := elimCoord z) p)
