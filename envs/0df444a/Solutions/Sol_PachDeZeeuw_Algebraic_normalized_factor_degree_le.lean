-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.normalized_factor_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:56.422769+00:00
-- url     : https://prove2.me/submissions/c0dfb4b1-32f3-4f31-9fc5-e9a13094ad98

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution {p h : MvPolynomial (Fin 2) ℝ} (hp0 : p ≠ 0)
    (hh : h ∈ UniqueFactorizationMonoid.normalizedFactors p) :
    h.totalDegree ≤ p.totalDegree := by
  have hdiv : h ∣ p := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hh
  exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hp0
