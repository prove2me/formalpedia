-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.resultant_ne_zero_of_fraction_coprime
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:57.696418+00:00
-- url     : https://prove2.me/submissions/e2a8c1a7-53ca-4b35-818c-85269d5d09b0

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (P Q : Polynomial XCoeff)
    (hcop : IsCoprime (P.map (algebraMap XCoeff XFrac))
                       (Q.map (algebraMap XCoeff XFrac))) :
    Polynomial.resultant P Q ≠ 0 := by
  intro hzero
  have hinj : Function.Injective (algebraMap XCoeff XFrac) :=
    IsFractionRing.injective XCoeff XFrac
  have hmapzero :
      Polynomial.resultant
        (P.map (algebraMap XCoeff XFrac))
        (Q.map (algebraMap XCoeff XFrac)) = 0 := by
    rw [show
        Polynomial.resultant
          (P.map (algebraMap XCoeff XFrac))
          (Q.map (algebraMap XCoeff XFrac)) =
        Polynomial.resultant
          (P.map (algebraMap XCoeff XFrac))
          (Q.map (algebraMap XCoeff XFrac))
          P.natDegree Q.natDegree by
      simp [Polynomial.natDegree_map_eq_of_injective hinj]]
    rw [Polynomial.resultant_map_map, hzero]
    simp
  exact Polynomial.resultant_ne_zero _ _ hcop hmapzero
