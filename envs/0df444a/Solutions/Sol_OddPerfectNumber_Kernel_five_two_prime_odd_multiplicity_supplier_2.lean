-- Prove2me | solution 2 for OddPerfectNumber.Kernel.five_two_prime_odd_multiplicity_supplier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T14:59:56.61173+00:00
-- url     : https://prove2.me/submissions/a377025e-815a-4305-b44f-6c227f9c8ec0

-- Target: OddPerfectNumber.Kernel.five_two_prime_odd_multiplicity_supplier
--         (81a21984-c732-49a9-a3b7-bc3ceec52ae7)
--
-- REPAIR of 6917 (v38), the CALC-CHAIN route.  2 groups read from ONE verified
-- 131-line capture; declared=2 captured=2, END OF CE REPORT groups=2
-- diagnostics=2, exit 0.
--
-- v38 introduced a genuine type error of its own making:
--
--   line 79: the argument
--     Nat.factorization_mul (pow_ne_zero 5 ...) hd1sq
--   has type
--     (p^5 * (d1^2 * (q*r))).factorization = (p^5).factorization + ...
--   but is expected to have type
--     p^5 * (d1^2 * (q*r)) = ?m
--   in the application congrArg (fun n => n.factorization l) (...)
--
-- The mistake: `congrArg` was applied to the RAW `Nat.factorization_mul`
-- equation (an equality of FINSUPPs), and then the resulting equality was
-- treated as if it were an equality of NATS.  The fix is to evaluate the
-- Finsupp equality at `l` FIRST (congrArg on the function, then
-- `Finsupp.add_apply`), which is exactly the idiom that 6903, 6918 and this
-- repair all use.
--
-- line 67 "No goals to be solved" was a cascade of the same step already
-- discharging the goal.
import Mathlib

theorem solution {p m d1 q r : Nat} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r)))
    (l : Nat) (hl : l.Prime)
    (hodd : Not (Even ((∑ d ∈ (m ^ 2).divisors, d).factorization l))) :
    (l = p \/ l = q \/ l = r) := by
  by_contra hcon
  have hneqp : l ≠ p := fun h => hcon (Or.inl h)
  have hneqq : l ≠ q := fun h => hcon (Or.inr (Or.inl h))
  have hneqr : l ≠ r := fun h => hcon (Or.inr (Or.inr h))
  have hl1 : l ≠ 1 := hl.ne_one
  have hlp : ¬ l ∣ p := fun hd => (Nat.dvd_prime hp).mp hd |> fun x => x.elim hl1 hneqp
  have hlq : ¬ l ∣ q := fun hd => (Nat.dvd_prime hq).mp hd |> fun x => x.elim hl1 hneqq
  have hlr : ¬ l ∣ r := fun hd => (Nat.dvd_prime hr).mp hd |> fun x => x.elim hl1 hneqr
  have hlqr : ¬ l ∣ q * r := fun hd => (hl.dvd_mul).mp hd |> fun x => x.elim hlq hlr
  have hd1n : d1 ≠ 0 := by
    intro hd10
    have hzz : (∑ d ∈ (m ^ 2).divisors, d) = 0 := by rw [h2, hd10]; simp
    exact hodd ⟨0, by rw [hzz, Nat.factorization_zero]; rfl⟩
  have hd1l : (d1 ^ 2).factorization l = 2 * d1.factorization l := by
    rw [Nat.factorization_pow]
    simp only [Finsupp.nsmul_apply, Nat.nsmul_eq_mul]
  have hp5 : p ^ 5 ≠ 0 := pow_ne_zero 5 hp.ne_zero
  have hd1sq : d1 ^ 2 ≠ 0 := pow_ne_zero 2 hd1n
  have hqr0 : q * r ≠ 0 := mul_ne_zero hq.ne_zero hr.ne_zero
  have hqrval : (q * r).factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd hlqr
  have hlpn : ¬ l ∣ p ^ 5 := fun hd => hlp (hl.dvd_of_dvd_pow hd)
  have hpval : p.factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd hlp
  -- Evaluate the Finsupp identities at `l` BEFORE using them as Nat equalities.
  have e1 := congrArg (fun f : ℕ →₀ ℕ => f l) (Nat.factorization_mul hp5 (Nat.mul_ne_zero hd1sq hqr0))
  simp only [Finsupp.add_apply] at e1
  have e2 := congrArg (fun f : ℕ →₀ ℕ => f l) (Nat.factorization_mul hd1sq hqr0)
  simp only [Finsupp.add_apply] at e2
  have e4 := congrArg (fun f : ℕ →₀ ℕ => f l) (Nat.factorization_pow (p : ℕ) (k := 5))
  simp only [Finsupp.nsmul_apply, Nat.nsmul_eq_mul] at e4
  -- A calc chain, so each equality is consumed at exactly the level it holds.
  have hsval :
      (p ^ 5 * (d1 ^ 2 * (q * r))).factorization l = 2 * d1.factorization l := by
    calc (p ^ 5 * (d1 ^ 2 * (q * r))).factorization l
        = (p ^ 5).factorization l + (d1 ^ 2 * (q * r)).factorization l := e1
      _ = (p ^ 5).factorization l
          + ((d1 ^ 2).factorization l + (q * r).factorization l) := by rw [e2]
      _ = 5 * p.factorization l
          + (2 * d1.factorization l + (q * r).factorization l) := by rw [e4, hd1l]
      _ = 2 * d1.factorization l := by rw [hpval, hqrval]; omega
  have heven : Even ((∑ d ∈ (m ^ 2).divisors, d).factorization l) := by
    rw [h2, hsval]
    exact ⟨d1.factorization l, by omega⟩
  exact hodd heven

