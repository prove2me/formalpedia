-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.ComplementTruncationPencil.eval_neg_truncationQuotient_at_root_yukon_277728d2fd36
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-29T22:28:17.84204+00:00
-- url     : https://prove2.me/submissions/63391bbb-02ad-403d-b6ae-1b3bcb035d09

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




import Mathlib
import Definitions.Def_Yukon_fce1ab10c536c75cdaab6eaf
/-!
# Complement truncation and a monomial pencil

Let `L * R = X^N - 1`, and split the complementary factor as

`R = X^s * H + r * X^(s - 1) + E`.

If `gamma * r = -1`, multiplying the resulting quotient candidate by `X^s`
gives an expression involving only the locator `L` and the short residual
tail `E`.  At every root of `L`, the negative quotient evaluates as the
two-monomial pencil

`x^(A - 1) + gamma * x^(N - s)`.

This is the exact algebraic bridge behind the complement-truncation syndrome
experiment.  It deliberately does not assert that the residual high band can
be cancelled: at the current benchmark agreement it still has `8709`
coefficients.
-/

namespace ProximityPrize.SubmissionUpper.ComplementTruncationPencil

open Polynomial

variable {F : Type} [Field F]
/-- At a root of the locator, the negative truncation quotient evaluates to
the corresponding two-monomial pencil value. -/
theorem _root_.solution
    {N A s : ℕ} {gamma x : F} {L H : Polynomial F}
    (hx : L.eval x = 0) :
    (-truncationQuotient N A s gamma L H).eval x =
      x ^ (A - 1) + gamma * x ^ (N - s)  := by
  simp only [truncationQuotient, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, hx, mul_zero, zero_mul, neg_sub]
  ring
end ComplementTruncationPencil
end SubmissionUpper
end ProximityPrize
