-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.normalized_factor_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:56.955456+00:00
-- url     : https://prove2.me/submissions/2eea737b-98d1-416f-8bc2-0dc1f6acfb9d

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution {p h : MvPolynomial (Fin 2) ℝ}
    (hh : h ∈ UniqueFactorizationMonoid.normalizedFactors p) :
    Irreducible h := by
  exact UniqueFactorizationMonoid.irreducible_of_normalized_factor h hh
