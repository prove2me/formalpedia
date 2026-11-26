-- Prove2me | solution 1 for continuous_coeff_divByMonic_X_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:42:44.497812+00:00
-- url     : https://prove2.me/submissions/0421e7e0-f2b4-48f4-86b4-f261188779fe

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (p : Polynomial ℂ) (n : ℕ) :
    Continuous (fun z : ℂ =>
      (p /ₘ (Polynomial.X - Polynomial.C z)).coeff n) := by
  have hfun :
      (fun z : ℂ => (p /ₘ (Polynomial.X - Polynomial.C z)).coeff n) =
      fun z => ∑ i ∈ Finset.Icc (n + 1) p.natDegree,
        z ^ (i - (n + 1)) * p.coeff i := by
    funext z
    rw [Polynomial.coeff_divByMonic_X_sub_C]
  rw [hfun]
  fun_prop
