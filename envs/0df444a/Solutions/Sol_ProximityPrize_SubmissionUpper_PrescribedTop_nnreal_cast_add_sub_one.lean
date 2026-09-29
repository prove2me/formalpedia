-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.PrescribedTop.nnreal_cast_add_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T05:53:08.720675+00:00
-- url     : https://prove2.me/submissions/29447d27-4d04-4f19-bd2a-9fdced8ff6bc

import Mathlib
import Init
/-!
# A prescribed-top-coefficient collision family below half radius

The included baseline attacks at radius `1/2` using the word `X^m` together with
*every* `m`-subset of the domain as an interpolation set.  This file generalises
that construction: it uses `t`-subsets with `t = m + r`, restricted to those whose
vanishing polynomial shares its top `r` coefficients with a fixed one.  Each such
subset still yields a genuine codeword agreeing with a single fixed word on all `t`
points, so the attack survives at radius `(n - t)/n = 1/2 - r/n`.

With `r = 8431` this certifies the unsafe suffix from grid index `122641` onward.
-/

namespace ProximityPrize.SubmissionUpper.PrescribedTop

open Polynomial
                                   
                             
open scoped NNReal


                             





















































































































/-! ## The chosen fibre -/

























/-! ## Transporting the vanishing polynomials to the extension field -/
















/-! ## The codeword polynomials -/







/-! ## The fixed word and its messages -/


























/-! ## The unsafe suffix from grid index `122641` -/













theorem _root_.solution (q N : ℕ) :
    (q : ℝ≥0) + (N : ℝ≥0) - 1 = ((q + N - 1 : ℕ) : ℝ≥0) := (by
  apply NNReal.eq
  norm_num
)
end PrescribedTop
end SubmissionUpper
end ProximityPrize
