-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.resultant_ne_zero_of_isRelPrime_primitive_curry
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:43:55.193268+00:00
-- url     : https://prove2.me/submissions/6ff23904-a44c-4c1b-81f0-d7d4d2f73329

import Mathlib
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_isRelPrime_fraction_map_of_isPrimitive
import Theorems.Thm_PachDeZeeuw_Algebraic_resultant_ne_zero_of_fraction_coprime

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve
namespace PachDeZeeuw.Algebraic

/-- Primitive `IsRelPrime` curries remain coprime after mapping to the fraction field. -/
theorem isCoprime_fraction_map_of_isPrimitive
    (P Q : Polynomial XCoeff)
    (hPprim : P.IsPrimitive)
    (hQprim : Q.IsPrimitive)
    (hrel : IsRelPrime P Q) :
    IsCoprime (P.map (algebraMap XCoeff XFrac))
              (Q.map (algebraMap XCoeff XFrac)) := by
  exact (isRelPrime_iff_isCoprime).1
    (isRelPrime_fraction_map_of_isPrimitive P Q hPprim hQprim hrel)

end PachDeZeeuw.Algebraic

open PachDeZeeuw.Algebraic in
theorem solution (p q : MvPolynomial (Fin 2) ℝ)
    (hpprim : (Curry0 p).IsPrimitive)
    (hqprim : (Curry0 q).IsPrimitive)
    (hrel : IsRelPrime (Curry0 p) (Curry0 q)) :
    Polynomial.resultant (Curry0 p) (Curry0 q) ≠ 0 := by
  exact resultant_ne_zero_of_fraction_coprime (Curry0 p) (Curry0 q)
    (isCoprime_fraction_map_of_isPrimitive (Curry0 p) (Curry0 q) hpprim hqprim hrel)
