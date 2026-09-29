-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.mem_CoeffLineZeroSet
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:55.317155+00:00
-- url     : https://prove2.me/submissions/70404c9b-72f4-4d46-8f1b-eb3645f34b9d

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution {a : MvPolynomial (Fin 1) ℝ}
    {p : Point2} :
    p ∈ CoeffLineZeroSet a ↔ MvPolynomial.eval (fun _ : Fin 1 => p 1) a = 0 := Iff.rfl
