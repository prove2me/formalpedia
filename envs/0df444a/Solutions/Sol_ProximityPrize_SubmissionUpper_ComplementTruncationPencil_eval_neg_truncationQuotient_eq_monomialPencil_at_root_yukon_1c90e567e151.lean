-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.ComplementTruncationPencil.eval_neg_truncationQuotient_eq_monomialPencil_at_root_yukon_1c90e567e151
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-29T22:57:46.627146+00:00
-- url     : https://prove2.me/submissions/66ff9c85-0eb4-45aa-a43d-5fbfba0ea5a7

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




import Mathlib
import Definitions.Def_Yukon_8a35bbbaa090b2d37c4699cd
import Definitions.Def_Yukon_c8e407f0f265709344b29f9b
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
/-- Equivalently, the two polynomials agree at every root of `L`. -/
theorem _root_.solution
    {N A s : ℕ} {gamma x : F} {L H : Polynomial F}
    (hx : L.eval x = 0) :
    (-truncationQuotient N A s gamma L H).eval x =
      (monomialPencil N A s gamma).eval x  := by
  rw [eval_neg_truncationQuotient_at_root hx]
  simp [monomialPencil]
end ComplementTruncationPencil
end SubmissionUpper
end ProximityPrize
