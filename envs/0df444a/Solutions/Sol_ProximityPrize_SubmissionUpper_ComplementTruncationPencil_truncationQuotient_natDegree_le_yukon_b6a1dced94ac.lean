-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.ComplementTruncationPencil.truncationQuotient_natDegree_le_yukon_b6a1dced94ac
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-29T22:57:43.07514+00:00
-- url     : https://prove2.me/submissions/5f9b0412-eaf9-4915-824b-3deaa52f7525

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




import Mathlib
import Definitions.Def_Yukon_01360736d0dae9976a68d3ed
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
/-- Multiplication by `X^s` transfers a degree bound on the residual side of
the identity back to the quotient. -/
theorem _root_.solution
    {N A s D : ℕ} {gamma r : F} {L R H E : Polynomial F}
    (hsN : s ≤ N) (hA : 1 ≤ A)
    (hgrid : L * R = Polynomial.X ^ N - 1)
    (htrunc : R = Polynomial.X ^ s * H +
      Polynomial.C r * Polynomial.X ^ (s - 1) + E)
    (hgamma : gamma * r = -1)
    (hresidual : (Polynomial.X ^ (s - 1) * L -
      Polynomial.X ^ (A + s - 1) - Polynomial.C gamma * L * E -
        Polynomial.C gamma).natDegree ≤ D + s) :
    (truncationQuotient N A s gamma L H).natDegree ≤ D  := by
  by_cases hQ : truncationQuotient N A s gamma L H = 0
  · simp [hQ]
  · have hX : (Polynomial.X : Polynomial F) ^ s ≠ 0 :=
      pow_ne_zero _ Polynomial.X_ne_zero
    have hbound : (Polynomial.X ^ s *
        truncationQuotient N A s gamma L H).natDegree ≤ D + s := by
      rw [X_pow_mul_truncationQuotient hsN hA hgrid htrunc hgamma]
      exact hresidual
    rw [Polynomial.natDegree_mul hX hQ, Polynomial.natDegree_X_pow] at hbound
    omega
end ComplementTruncationPencil
end SubmissionUpper
end ProximityPrize
