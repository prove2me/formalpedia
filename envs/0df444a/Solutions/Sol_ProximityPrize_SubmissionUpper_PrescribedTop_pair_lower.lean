-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.PrescribedTop.pair_lower
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T18:01:56.919143+00:00
-- url     : https://prove2.me/submissions/3da26305-c14c-4bce-9f1f-fb7727ba0e23

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


                             

















































/-- Along a segment of constant sum, the product is smallest at the ends. -/
theorem _root_.solution (A k i : ℕ) (hik : i ≤ k) :
    (A + k) * A ≤ (A + (k - i)) * (A + i) := (by
  obtain ⟨d, hd⟩ := Nat.le.dest hik
  subst hd
  simp only [Nat.add_sub_cancel_left]
  nlinarith
)
end PrescribedTop
end SubmissionUpper
end ProximityPrize
