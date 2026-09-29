-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.PrescribedTop.choose_shift
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T05:38:37.769391+00:00
-- url     : https://prove2.me/submissions/395d49d2-b1c5-4878-b412-c1cf59458fb1

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


                             



























































theorem _root_.solution (N a : ℕ) : ∀ b : ℕ,
    N.choose (a + b) * (∏ i ∈ Finset.range b, (a + 1 + i))
      = N.choose a * (∏ i ∈ Finset.range b, (N - a - i)) := (by
  intro b
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      have hstep : N.choose (a + b + 1) * (a + b + 1) = N.choose (a + b) * (N - (a + b)) :=
        Nat.choose_succ_right_eq N (a + b)
      calc
        N.choose (a + (b + 1)) * ((∏ i ∈ Finset.range b, (a + 1 + i)) * (a + 1 + b))
            = (N.choose (a + b + 1) * (a + b + 1)) * (∏ i ∈ Finset.range b, (a + 1 + i)) := by
              rw [show a + (b + 1) = a + b + 1 by omega, show a + 1 + b = a + b + 1 by omega]
              ring
        _ = (N.choose (a + b) * (N - (a + b))) * (∏ i ∈ Finset.range b, (a + 1 + i)) := by
              rw [hstep]
        _ = (N.choose (a + b) * (∏ i ∈ Finset.range b, (a + 1 + i))) * (N - (a + b)) := by ring
        _ = (N.choose a * (∏ i ∈ Finset.range b, (N - a - i))) * (N - (a + b)) := by rw [ih]
        _ = N.choose a * ((∏ i ∈ Finset.range b, (N - a - i)) * (N - a - b)) := by
              rw [show N - (a + b) = N - a - b by omega]; ring
)
end PrescribedTop
end SubmissionUpper
end ProximityPrize
