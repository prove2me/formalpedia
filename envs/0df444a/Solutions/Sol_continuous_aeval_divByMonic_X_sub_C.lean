-- Prove2me | solution 1 for continuous_aeval_divByMonic_X_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:48:07.378136+00:00
-- url     : https://prove2.me/submissions/3396f3b7-b3ad-446d-afed-e28661fc1fbb

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (p : Polynomial ℂ) :
    Continuous (fun z : ℂ =>
      Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z))) := by
  have hfun :
      (fun z : ℂ => Polynomial.aeval A
        (p /ₘ (Polynomial.X - Polynomial.C z))) =
      fun z => ∑ i ∈ Finset.range (p.natDegree + 1),
        (∑ j ∈ Finset.Icc (i + 1) p.natDegree,
          z ^ (j - (i + 1)) * p.coeff j) • A ^ i := by
    funext z
    rw [Polynomial.aeval_eq_sum_range' (x := A) (n := p.natDegree + 1)]
    · congr 1 with i
      rw [Polynomial.coeff_divByMonic_X_sub_C]
    · rw [Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C z),
        Polynomial.natDegree_X_sub_C]
      omega
  rw [hfun]
  fun_prop
