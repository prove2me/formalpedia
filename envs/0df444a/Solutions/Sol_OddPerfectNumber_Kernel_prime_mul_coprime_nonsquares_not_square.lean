-- Prove2me | solution 1 for OddPerfectNumber.Kernel.prime_mul_coprime_nonsquares_not_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T14:09:16.998325+00:00
-- url     : https://prove2.me/submissions/578b95e3-60b0-44e8-87c8-310aee4c0780

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- A prime times two coprime non-squares is never a square.
--
-- This is the elementary parity-toggling fact that replaces the deep
-- quadratic-order input of Hirakawa on the k=5 branch.  Coprimality forces each
-- of `a` and `b` to supply a prime of odd multiplicity, and makes those two
-- primes distinct; the single extra factor `q` can repair the parity at only
-- one of them, so at the other an odd multiplicity survives.
--
-- The even-factorization bridge `OddPerfectNumber.Kernel.isSq_iff_even_factorization`
-- (theorem 28b00e2d-2e78-4683-8075-7135bec4a50b) is `Proved`, so the witness
-- construction is no longer needed here: the square hypothesis supplies the
-- even-exponent hypothesis directly through the bridge, and only the
-- forward direction `exists_odd_exponent` is proved locally.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_isSq_iff_even_factorization

namespace OddPerfectNumber.Kernel
namespace Toggle

/-- Some prime occurs to an odd exponent in a non-square natural number. -/
theorem exists_odd_exponent {n : Nat} (hn0 : n ≠ 0) (hnsq : ¬ ∃ y, y ^ 2 = n) :
    ∃ p, ¬ Even (n.factorization p) := by
  by_contra hcon
  push_neg at hcon
  exact hnsq ((isSq_iff_even_factorization hn0).mpr hcon)

theorem prime_mul_coprime_nonsquares_not_square {a b q : Nat}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a.Coprime b)
    (hna : ¬ ∃ y, y ^ 2 = a) (hnb : ¬ ∃ y, y ^ 2 = b) (hq : q.Prime) :
    ¬ ∃ y, y ^ 2 = q * a * b := by
  classical
  intro hsq
  -- `a` and `b` each supply a witness prime of odd exponent.
  obtain ⟨r, hrodd⟩ := exists_odd_exponent ha0 hna
  obtain ⟨t, htodd⟩ := exists_odd_exponent hb0 hnb
  -- `¬ Even e` forces `e ≠ 0`: if `e = 0` then `e = 0 + 0` is even.
  have hr0 : a.factorization r ≠ 0 := fun hz => hrodd (by rw [hz]; exact ⟨0, rfl⟩)
  have ht0 : b.factorization t ≠ 0 := fun hz => htodd (by rw [hz]; exact ⟨0, rfl⟩)
  have hra : r ∣ a := Nat.dvd_of_factorization_pos hr0
  have htb : t ∣ b := Nat.dvd_of_factorization_pos ht0
  -- A nonzero exponent forces the base to be prime, by `factorization_eq_zero_iff`.
  have hrpr : r.Prime := by
    by_contra hn
    exact hr0 (by rw [Nat.factorization_eq_zero_iff a r]; exact Or.inl hn)
  have htpr : t.Prime := by
    by_contra hn
    exact ht0 (by rw [Nat.factorization_eq_zero_iff b t]; exact Or.inl hn)
  -- Coprimality makes the two witness primes distinct.  Restate `hab` at `r`
  -- using `Nat.Coprime.of_dvd_left` together with `Nat.coprime_comm`, so that
  -- `Prime.coprime_iff_not_dvd` (stated for `Coprime r b`) applies directly.
  have hbr : r.Coprime b := Nat.Coprime.of_dvd_left hra hab
  have hta' : t.Coprime a := Nat.Coprime.of_dvd_left htb (Nat.coprime_comm.mpr hab)
  have hrb : ¬ r ∣ b := (hrpr.coprime_iff_not_dvd).mp hbr
  have hta : ¬ t ∣ a := (htpr.coprime_iff_not_dvd).mp hta'
  have hrt : r ≠ t := fun h => hrb (h ▸ htb)
  -- The square hypothesis forces every exponent of `q * a * b` to be even.
  have hqab0 : q * a * b ≠ 0 := mul_ne_zero (mul_ne_zero hq.ne_zero ha0) hb0
  obtain ⟨y, hy⟩ := hsq
  have hall : ∀ p : Nat, Even ((q * a * b).factorization p) :=
    (isSq_iff_even_factorization hqab0).mp ⟨y, hy⟩
  -- At a prime `s ≠ q` the factor `q` contributes exponent `0`, so the exponent
  -- of `q * a * b` is exactly the sum of the exponents in `a` and `b`.
  have key : ∀ s : Nat, s ≠ q →
      (q * (a * b)).factorization s = a.factorization s + b.factorization s := by
    intro s hsq'
    -- `factorization` lands in `ℕ →₀ ℕ`, so a `Finsupp` equation must be
    -- specialised with `congrArg (fun f : ℕ →₀ ℕ => f s)` rather than `congrFun`.
    have hfac := congrArg (fun f : ℕ →₀ ℕ => f s)
      (Nat.factorization_mul hq.ne_zero (mul_ne_zero ha0 hb0))
    -- Open the `Finsupp` addition, and split `a * b` separately: rewriting it in
    -- place would need a `(q * a).factorization` term that is not present.
    have hinner := congrArg (fun f : ℕ →₀ ℕ => f s)
      (Nat.factorization_mul ha0 hb0)
    rw [Finsupp.add_apply, hinner] at hfac
    have hqf : q.factorization s = 0 := by
      -- `Nat.Prime.factorization` tests `q = s`, while `hsq'` is `s ≠ q`.
      rw [Nat.Prime.factorization hq, Finsupp.single_apply, if_neg (Ne.symm hsq')]
    -- `Finsupp.add_apply` has already exposed the summands, so only the
    -- arithmetic normalisation `0 + x = x` remains.
    rw [hqf, zero_add] at hfac
    exact hfac
  -- Either `r ≠ q` or `t ≠ q`, since `r ≠ t`.
  by_cases hrq : r = q
  · -- Then `t ≠ q`, and at `t` the exponent is that of `b` alone, which is odd.
    have htq : t ≠ q := fun h => hrt (hrq.trans h.symm)
    have htaf : a.factorization t = 0 := Nat.factorization_eq_zero_of_not_dvd hta
    have hsum : (q * a * b).factorization t = b.factorization t := by
      rw [show (q * a * b).factorization t = (q * (a * b)).factorization t from
        congrArg (fun n : Nat => n.factorization t) (Nat.mul_assoc q a b)]
      rw [key t htq, htaf, zero_add]
    exact absurd (hsum ▸ hall t) htodd
  · -- Then at `r` the exponent is that of `a` alone, which is odd.
    have hbtf : b.factorization r = 0 := Nat.factorization_eq_zero_of_not_dvd hrb
    have hsum : (q * a * b).factorization r = a.factorization r := by
      rw [show (q * a * b).factorization r = (q * (a * b)).factorization r from
        congrArg (fun n : Nat => n.factorization r) (Nat.mul_assoc q a b)]
      rw [key r hrq, hbtf, add_zero]
    exact absurd (hsum ▸ hall r) hrodd

end Toggle
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {a b q : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a.Coprime b)
    (hna : ¬ ∃ y, y ^ 2 = a) (hnb : ¬ ∃ y, y ^ 2 = b) (hq : q.Prime) :
    ¬ ∃ y, y ^ 2 = q * a * b :=
  OddPerfectNumber.Kernel.Toggle.prime_mul_coprime_nonsquares_not_square ha0 hb0 hab hna hnb hq
