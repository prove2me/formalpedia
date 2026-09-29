-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.curry_isPrimitive_of_irreducible_positive_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:51.624025+00:00
-- url     : https://prove2.me/submissions/b2ebed0b-9dc2-4d03-9f27-cc3364c8d428

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (h : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h)
    (hpos : 0 < (Curry0 h).natDegree) :
    (Curry0 h).IsPrimitive := by
  have hnd : ¬ (Curry0 h).natDegree = 0 := by
    exact Nat.ne_of_gt hpos
  simpa [Curry0] using
    (hh.map (MvPolynomial.finSuccEquiv ℝ 1).toRingEquiv).isPrimitive hnd
