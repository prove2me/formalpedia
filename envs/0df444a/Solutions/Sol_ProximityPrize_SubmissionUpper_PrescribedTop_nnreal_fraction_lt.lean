-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.PrescribedTop.nnreal_fraction_lt
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T05:33:46.798933+00:00
-- url     : https://prove2.me/submissions/428d9fd2-d808-4872-846c-9b3d7b4cd111

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
















theorem _root_.solution (q N k : ℕ) (hk : 0 < k) (hd : 0 < q + N - 1)
    (h : q + N - 1 < N * k) :
    (1 : ℝ≥0) / (k : ℝ≥0) <
      (N : ℝ≥0) / ((q + N - 1 : ℕ) : ℝ≥0) := (by
  have hk' : (0 : ℝ≥0) < (k : ℝ≥0) := by exact_mod_cast hk
  have hd' : (0 : ℝ≥0) < ((q + N - 1 : ℕ) : ℝ≥0) := by exact_mod_cast hd
  rw [div_lt_div_iff₀ hk' hd']
  norm_num
  exact_mod_cast h
)
end PrescribedTop
end SubmissionUpper
end ProximityPrize
