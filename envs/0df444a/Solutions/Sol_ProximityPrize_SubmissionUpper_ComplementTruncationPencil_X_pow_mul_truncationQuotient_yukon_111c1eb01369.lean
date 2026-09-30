-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.ComplementTruncationPencil.X_pow_mul_truncationQuotient_yukon_111c1eb01369
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-29T22:28:50.944988+00:00
-- url     : https://prove2.me/submissions/d3470fa0-7d80-4506-9169-f78949801172

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
/-- The complement-truncation identity.  The hypotheses `s ≤ N` and
`1 ≤ A` are exactly what is needed to recombine the truncated exponents. -/
theorem _root_.solution
    {N A s : ℕ} {gamma r : F} {L R H E : Polynomial F}
    (hsN : s ≤ N) (hA : 1 ≤ A)
    (hgrid : L * R = Polynomial.X ^ N - 1)
    (htrunc : R = Polynomial.X ^ s * H +
      Polynomial.C r * Polynomial.X ^ (s - 1) + E)
    (hgamma : gamma * r = -1) :
    Polynomial.X ^ s * truncationQuotient N A s gamma L H =
      Polynomial.X ^ (s - 1) * L - Polynomial.X ^ (A + s - 1) -
        Polynomial.C gamma * L * E - Polynomial.C gamma  := by
  have hXN : (Polynomial.X : Polynomial F) ^ s * Polynomial.X ^ (N - s) =
      Polynomial.X ^ N := by
    rw [← pow_add]
    congr 1
    omega
  have hXA : (Polynomial.X : Polynomial F) ^ s * Polynomial.X ^ (A - 1) =
      Polynomial.X ^ (A + s - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hH : (Polynomial.X : Polynomial F) ^ s * H =
      R - Polynomial.C r * Polynomial.X ^ (s - 1) - E := by
    linear_combination -htrunc
  dsimp only [truncationQuotient]
  calc
    Polynomial.X ^ s *
        (Polynomial.C gamma * L * H -
          Polynomial.C gamma * Polynomial.X ^ (N - s) -
            Polynomial.X ^ (A - 1)) =
        Polynomial.C gamma * L * (Polynomial.X ^ s * H) -
          Polynomial.C gamma * (Polynomial.X ^ s * Polynomial.X ^ (N - s)) -
            Polynomial.X ^ s * Polynomial.X ^ (A - 1) := by ring
    _ =
        Polynomial.C gamma * L * (Polynomial.X ^ s * H) -
          Polynomial.C gamma * Polynomial.X ^ N -
            Polynomial.X ^ (A + s - 1) := by
      rw [hXN, hXA]
    _ = Polynomial.C gamma * L *
          (R - Polynomial.C r * Polynomial.X ^ (s - 1) - E) -
          Polynomial.C gamma * Polynomial.X ^ N -
            Polynomial.X ^ (A + s - 1) := by rw [hH]
    _ = Polynomial.C gamma * (L * R) -
          (Polynomial.C gamma * Polynomial.C r) *
            (Polynomial.X ^ (s - 1) * L) - Polynomial.C gamma * L * E -
              Polynomial.C gamma * Polynomial.X ^ N -
                Polynomial.X ^ (A + s - 1) := by ring
    _ = Polynomial.C gamma * (Polynomial.X ^ N - 1) -
          (Polynomial.C gamma * Polynomial.C r) *
            (Polynomial.X ^ (s - 1) * L) - Polynomial.C gamma * L * E -
              Polynomial.C gamma * Polynomial.X ^ N -
                Polynomial.X ^ (A + s - 1) := by rw [hgrid]
    _ = Polynomial.X ^ (s - 1) * L - Polynomial.X ^ (A + s - 1) -
          Polynomial.C gamma * L * E - Polynomial.C gamma := by
      simp only [← Polynomial.C_mul, hgamma, Polynomial.C_neg,
        Polynomial.C_1]
      ring
end ComplementTruncationPencil
end SubmissionUpper
end ProximityPrize
