-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_two_prime_odd_multiplicity_supplier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T14:58:19.314432+00:00
-- url     : https://prove2.me/submissions/adb95f1e-5950-43f9-8d2a-6dc675447600

-- Target: OddPerfectNumber.Kernel.five_two_prime_odd_multiplicity_supplier
--         (81a21984-c732-49a9-a3b7-bc3ceec52ae7)
--
-- REPAIR of 6918 (v39).  1 group read from ONE verified 177-line capture;
-- declared=1 captured=1, END OF CE REPORT groups=1 diagnostics=1, exit 0.
--
-- v39 reduced 6903's 7 groups to ONE, and that single group is pure rewrite
-- ORDER.  Lean accepted the whole architecture: its goal state carries
--
--   e1 : (p^5 * (d1^2 * (q*r))).factorization l
--          = (p^5).factorization l + (d1^2 * (q*r)).factorization l
--   e2 : (d1^2 * (q*r)).factorization l
--          = (d1^2).factorization l + (q*r).factorization l
--   e4 : (p^5).factorization l = 5 * p.factorization l
--   hd1l, hp5val, hqrval : the three zero/normalisation facts
--   |- 5 * p.factorization l + (2 * d1.factorization l + (q*r).factorization l)
--        = 2 * d1.factorization l
--
-- v39 wrote `rw [e1, e2, hd1l, e4, hp5val, hqrval]`, but after `e4` fires the
-- LHS no longer contains `(p^5).factorization l`, so `hp5val` had nothing to
-- rewrite and Lean reported the pattern-not-found error naming `p.factorization l`
-- -- the residual form.  The fix is to rewrite the zero facts at the level where
-- they actually occur, in the order the goal state shows.
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
  -- zero the two factors whose `l`-exponent is unavailable, at the level where
  -- the exponent actually occurs.
  have hqrval : (q * r).factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd hlqr
  have hlpn : ¬ l ∣ p ^ 5 := fun hd => hlp (hl.dvd_of_dvd_pow hd)
  have hpval : p.factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd hlp
  -- additive factorization identities; NO coprimality is asserted anywhere.
  have e1 := congrArg (fun f : ℕ →₀ ℕ => f l) (Nat.factorization_mul hp5 (Nat.mul_ne_zero hd1sq hqr0))
  simp only [Finsupp.add_apply] at e1
  have e2 := congrArg (fun f : ℕ →₀ ℕ => f l) (Nat.factorization_mul hd1sq hqr0)
  simp only [Finsupp.add_apply] at e2
  have e4 := congrArg (fun f : ℕ →₀ ℕ => f l) (Nat.factorization_pow (p : ℕ) (k := 5))
  simp only [Finsupp.nsmul_apply, Nat.nsmul_eq_mul] at e4
  have hsval :
      (p ^ 5 * (d1 ^ 2 * (q * r))).factorization l = 2 * d1.factorization l := by
    -- REPAIR: rewrite `hpval` and `hqrval` at the levels where they occur
    -- (`p.factorization l` and `(q * r).factorization l`), never at
    -- `(p^5).factorization l`, which `e4` has already eliminated.
    rw [e1, e2, hd1l, e4, hpval, hqrval]
    omega
  have heven : Even ((∑ d ∈ (m ^ 2).divisors, d).factorization l) := by
    rw [h2, hsval]
    exact ⟨d1.factorization l, by omega⟩
  exact hodd heven

