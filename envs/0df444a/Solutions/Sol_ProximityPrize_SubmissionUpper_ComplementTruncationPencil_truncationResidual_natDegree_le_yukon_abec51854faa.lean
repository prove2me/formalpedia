-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.ComplementTruncationPencil.truncationResidual_natDegree_le_yukon_abec51854faa
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-29T22:18:37.553287+00:00
-- url     : https://prove2.me/submissions/8d66dcc9-31aa-4f1d-95c5-29906c9a6428

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




import Mathlib
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
/-- If the locator is monic of degree `A` and `E` is the residual tail below
`X^(s - 1)`, then the leading terms in the residual identity cancel. -/
theorem _root_.solution
    {A s : ℕ} {gamma : F} {L E : Polynomial F}
    (hs : 2 ≤ s) (hA : 1 ≤ A) (hLmonic : L.Monic)
    (hLdegree : L.natDegree = A) (hE : E.natDegree ≤ s - 2) :
    (Polynomial.X ^ (s - 1) * L - Polynomial.X ^ (A + s - 1) -
      Polynomial.C gamma * L * E - Polynomial.C gamma).natDegree ≤
        A + s - 2  := by
  have hlead : (Polynomial.X ^ (s - 1) * L -
      Polynomial.X ^ (A + s - 1)).natDegree ≤ A + s - 2 := by
    have hproductDegree : (Polynomial.X ^ (s - 1) * L).natDegree = A + s - 1 := by
      rw [Polynomial.natDegree_X_pow_mul (s - 1) hLmonic.ne_zero, hLdegree]
      omega
    have htop : (Polynomial.X ^ (s - 1) * L).coeff (A + s - 1) = 1 := by
      calc
        (Polynomial.X ^ (s - 1) * L).coeff (A + s - 1) = L.coeff A := by
          rw [show A + s - 1 = A + (s - 1) by omega]
          exact Polynomial.coeff_X_pow_mul L (s - 1) A
        _ = 1 := by rw [← hLdegree]; exact hLmonic.coeff_natDegree
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    have hnj : A + s - 1 ≤ j := by omega
    by_cases hjn : j = A + s - 1
    · subst j
      rw [Polynomial.coeff_sub, htop, Polynomial.coeff_X_pow_self, sub_self]
    · have hnltj : A + s - 1 < j :=
        lt_of_le_of_ne hnj (fun h ↦ hjn h.symm)
      rw [Polynomial.coeff_sub,
        Polynomial.coeff_eq_zero_of_natDegree_lt (hproductDegree.symm ▸ hnltj),
        Polynomial.coeff_eq_zero_of_natDegree_lt
          ((Polynomial.natDegree_X_pow (R := F) (A + s - 1)).symm ▸ hnltj),
        sub_zero]
  have htail : (Polynomial.C gamma * L * E).natDegree ≤ A + s - 2 := by
    calc
      (Polynomial.C gamma * L * E).natDegree ≤
          (Polynomial.C gamma * L).natDegree + E.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (Polynomial.C gamma).natDegree + L.natDegree + E.natDegree := by
        exact Nat.add_le_add_right Polynomial.natDegree_mul_le _
      _ ≤ A + s - 2 := by
        rw [Polynomial.natDegree_C, hLdegree]
        omega
  have hconstant : (Polynomial.C gamma : Polynomial F).natDegree ≤ A + s - 2 := by
    rw [Polynomial.natDegree_C]
    omega
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le
      ((Polynomial.natDegree_sub_le _ _).trans (max_le hlead htail))
      hconstant)
end ComplementTruncationPencil
end SubmissionUpper
end ProximityPrize
