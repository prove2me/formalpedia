-- Prove2me | solution 1 for OddPerfectNumber.Kernel.coprime_sq_factor_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T18:45:31.650337+00:00
-- url     : https://prove2.me/submissions/81c23445-ec6f-48ba-961c-44fab3da6fba

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Extracting a square factor from a coprime square product.
--
-- If `a` and `b` are coprime, both nonzero, and `a * b` is a square, then each
-- of `a` and `b` is a square.  This is the standard coprime-product lemma, and
-- it is what the `k = 5` factorisation needs: once
--
--     ((p + 1) / 2) * (p ^ 2 - p + 1)
--
-- is known to be a square and the two factors are known to be coprime, the
-- second factor must be a square, contradicting
-- `five_cyclotomic_factors_ne_square`.
--
-- Mathlib has no `Nat.IsSquare`, so the statement is phrased with `exists y,
-- y ^ 2 = _` to match the accepted children.  The proof goes through exponent
-- parity using the accepted bridge
-- `OddPerfectNumber.Kernel.isSq_iff_even_factorization`
-- (theorem 28b00e2d-2e78-4683-8075-7135bec4a50b): at each prime the total
-- multiplicity is even, and coprimality means only one factor contributes.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_isSq_iff_even_factorization

namespace OddPerfectNumber.Kernel
namespace Extract

theorem coprime_sq_factor_right {a b : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : a.Coprime b) (hsq : ∃ y, y ^ 2 = a * b) :
    ∃ z, z ^ 2 = b := by
  have hab0 : a * b ≠ 0 := mul_ne_zero ha0 hb0
  have heven : ∀ p : Nat, Even ((a * b).factorization p) :=
    (isSq_iff_even_factorization hab0).mp hsq
  -- `Nat.factorization_mul` splits the multiplicity additively.
  have hfac : (a * b).factorization = a.factorization + b.factorization :=
    Nat.factorization_mul ha0 hb0
  refine (isSq_iff_even_factorization hb0).mpr ?_
  intro p
  by_cases hpd : p ∣ b
  · -- `a` contributes nothing at `p`.  If `p ∣ a` as well, coprimality forces
    -- `p = 1`, and `1` carries no multiplicity; otherwise
    -- `Nat.factorization_eq_zero_of_not_dvd` applies directly.
    have ha0fac : a.factorization p = 0 := by
      by_cases hpa : p ∣ a
      · have hd : p ∣ Nat.gcd a b := dvd_gcd hpa hpd
        have hd1 : p ∣ 1 := by rw [← hab.gcd_eq_one]; exact hd
        have hp1 : p = 1 := Nat.dvd_one.mp hd1
        subst hp1
        simp
      · exact Nat.factorization_eq_zero_of_not_dvd hpa
    -- `(a * b).factorization p = a.factorization p + b.factorization p`, and
    -- the left summand vanishes, so the total is `b`'s multiplicity at `p`.
    -- `happ : (a * b).factorization p = a.factorization p + b.factorization p`.
    -- Push it into the evenness hypothesis, then drop the vanished summand, so
    -- the goal `Even (b.factorization p)` is exactly what remains.
    have happ := congrArg (fun f : ℕ →₀ ℕ => f p) hfac
    simp only [Finsupp.add_apply, add_assoc] at happ
    -- Push the factorisation split into the evenness hypothesis and let `simp`
    -- close the arithmetic; `Even (0 + n)` reduces to `Even n` by `zero_add`.
    have h := heven p
    rw [happ, ha0fac] at h
    simpa using h
  · have hb0fac : b.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpd
    exact (Nat.even_iff).mpr (by simp [hb0fac])

end Extract
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {a b : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : a.Coprime b) (hsq : ∃ y, y ^ 2 = a * b) :
    ∃ z, z ^ 2 = b :=
  OddPerfectNumber.Kernel.Extract.coprime_sq_factor_right ha0 hb0 hab hsq
