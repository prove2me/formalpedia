-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.specialized_natDegree_le_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:58.229725+00:00
-- url     : https://prove2.me/submissions/d18fe660-7f63-40c9-9ef2-556c8c12221e

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (p : MvPolynomial (Fin 2) ℝ) (x : ℝ) :
    (Specialized0 x p).natDegree ≤ p.totalDegree := by
  calc
    (Specialized0 x p).natDegree ≤ (Curry0 p).natDegree := by
      simpa [Specialized0] using
        (Polynomial.natDegree_map_le (f := coeffEval x) (p := Curry0 p))
    _ = MvPolynomial.degreeOf 0 p := by
      simpa [Curry0] using
        (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 1) p)
    _ ≤ p.totalDegree := MvPolynomial.degreeOf_le_totalDegree p 0
