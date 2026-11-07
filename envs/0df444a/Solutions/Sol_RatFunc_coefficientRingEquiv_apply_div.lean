-- Prove2me | solution 1 for RatFunc.coefficientRingEquiv_apply_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:54:13.19021+00:00
-- url     : https://prove2.me/submissions/922168b6-c307-42fa-be45-bd016b25e450

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_RatFuncCoefficientEquiv

set_option autoImplicit false
open RatFunc
namespace RatFunc
theorem _root_.solution
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (p q : Polynomial K) :
    coefficientRingEquiv e
        (algebraMap (Polynomial K) (RatFunc K) p /
          algebraMap (Polynomial K) (RatFunc K) q) =
      algebraMap (Polynomial L) (RatFunc L) (Polynomial.mapEquiv e p) /
        algebraMap (Polynomial L) (RatFunc L) (Polynomial.mapEquiv e q) := by
  let ep : Polynomial K ≃+* Polynomial L := Polynomial.mapEquiv e
  let hnonzero : nonZeroDivisors (Polynomial K) ≤
      (nonZeroDivisors (Polynomial L)).comap ep :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ep ep.injective
  change RatFunc.map ep hnonzero
      (algebraMap (Polynomial K) (RatFunc K) p /
        algebraMap (Polynomial K) (RatFunc K) q) = _
  exact RatFunc.map_apply_div ep hnonzero p q
end RatFunc
