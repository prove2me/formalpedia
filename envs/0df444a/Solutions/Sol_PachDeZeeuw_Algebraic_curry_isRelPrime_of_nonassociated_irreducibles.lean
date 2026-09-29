-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.curry_isRelPrime_of_nonassociated_irreducibles
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:52.245388+00:00
-- url     : https://prove2.me/submissions/d8a505a1-283b-4d1d-a5d2-f143c6024ded

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (h k : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h) (hk : Irreducible k)
    (hnot : ¬ Associated h k) :
    IsRelPrime (Curry0 h) (Curry0 k) := by
  have hhC : Irreducible (Curry0 h) := by
    simpa [Curry0] using (hh.map (MvPolynomial.finSuccEquiv ℝ 1).toRingEquiv)
  refine (hhC.isRelPrime_iff_not_dvd).2 ?_
  intro hdiv
  have hkdiv' : h ∣ (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 k) := by
    exact (map_dvd_iff_dvd_symm (MvPolynomial.finSuccEquiv ℝ 1)).1 hdiv
  have hkdiv : h ∣ k := by
    simpa [Curry0] using hkdiv'
  exact hnot (hh.associated_of_dvd hk hkdiv)
