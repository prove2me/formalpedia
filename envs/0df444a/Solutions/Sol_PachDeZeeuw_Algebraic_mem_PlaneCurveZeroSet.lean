-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.mem_PlaneCurveZeroSet
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:55.839696+00:00
-- url     : https://prove2.me/submissions/df71c298-1621-4a53-9769-74f2582a05bf

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution {p : MvPolynomial (Fin 2) ℝ}
    {x : Point2} :
    x ∈ PlaneCurveZeroSet p ↔ MvPolynomial.eval (fun i => x i) p = 0 := Iff.rfl
