-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_dris_one_index_not_dvd_euler
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T12:14:13.682986+00:00
-- url     : https://prove2.me/submissions/e9da8326-ad3e-4852-8980-c97316723a9b

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.five_dris_one_index_not_dvd_euler
--          a4779371-6f2d-462b-bd92-b5faaaa9d30c
--
-- The Euler prime does not divide the Dris index.
--
-- This closes the one hypothesis the p-adic budget argument needs and that the
-- residual `five_no_two_prime_squarefree_index` (6eb10265) does not supply as a
-- hypothesis.  That target assumes only `Not (Dvd.dvd p m)`; the statement
-- `Not (Dvd.dvd p (d1 ^ 2 * (q * r)))` has to be derived, and it follows from
-- the FIRST Dris equation alone.
--
-- Argument.  The index occurs as a factor of the right hand side of h1, so
-- `p | index` forces `p | 2 * m ^ 2`.  Primality lifts this to `p | m` or
-- `p | 2`; the second is excluded by `p != 2` (equivalently `p` is odd), and
-- the first contradicts `hpm`.  No case split on `d1`, `q` or `r` is needed,
-- and `q`, `r` are not even used.
--
-- Consequence.  With this, the second Dris equation `sigma(m^2) = p^5 * s`
-- gives `(sigma(m^2)).factorization p = 5` via
-- `factorization_p_of_mul_prime_pow_ne` (925fa028), which is exactly the rigid
-- budget that the odd-local-valuation source `index_prime_has_odd_multiplicity_source`
-- (48e8fb88) then splits.
--
-- Diagnostic notes.  `Nat.dvd_prime hp` has type
--   `p ∣ a * b -> (p ∣ a ∨ p ∣ b)`
-- so the disjunction splits the *left* factor from the right one: applying it to
-- `p ∣ 2 * m ^ 2` yields `p ∣ 2 ∨ p ∣ m ^ 2`, not `p = 2 ∨ ...`.  That is the
-- orientation used in the accepted `solution_q29_half_exp3_ne_three_v1.lean:98`.
-- The `p ∣ 2` branch is killed by `p != 2` via `hp.ne_two` / primality, and
-- `p ∣ m ^ 2` is lifted to `p ∣ m` by `Prime.dvd_of_dvd_pow`, as in
-- `89b_FiveIndexSourceNotSelf.lean` in this directory.
import Mathlib

namespace OddPerfectNumber.Kernel
namespace EulerIdx

theorem solution_aux {p m d1 q r : Nat} (hp : p.Prime)
    (hp2 : p != 2) (hpm : Not (Dvd.dvd p m))
    (h1 : 2 * m ^ 2 =
      (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r))) :
    Not (Dvd.dvd p (d1 ^ 2 * (q * r))) := by
  intro hps
  have hdvd : Dvd.dvd p (2 * m ^ 2) := by
    -- `dvd_mul_of_dvd_right : a ∣ b → a ∣ c * b`, which puts the ORIGINAL
    -- divisibility on the RIGHT of the product, matching the shape of the
    -- factorisation in `h1`.  Candidate 5508 failed with
    --   p ∣ d1^2*(q*r) * (...) but is expected to have type
    --   p ∣ (...) * (d1^2*(q*r))
    -- because `dvd_mul_of_dvd_left` appends the multiplier on the right.
    -- The accepted corpus uses this exact form at
    -- `solution_q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4.lean:27`.
    have hmul : Dvd.dvd p
        (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1)) * (d1 ^ 2 * (q * r))) :=
      dvd_mul_of_dvd_right hps
        (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1)))
    rwa [← h1] at hmul
  -- `Nat.dvd_prime hp` has type `a ∣ b -> (p ∣ a ∨ p ∣ b)` ONLY when the
  -- dividend `b` is literally a product `a * c`.  The remote reported
  --   hdvd' has type p ∣ m ^ 2 * 2 but is expected to have type ?m ∣ p
  -- so the `.mp` argument is the divisibility of the LEFT FACTOR `a` and the
  -- PRODUCT hypothesis is a separate argument.  The accepted usage at
  -- `solution_q29_half_exp3_ne_three_v1.lean:98` is
  -- `(Nat.dvd_prime Nat.prime_two).mp hdvd` with `hdvd : orderOf .. ∣ 2`, i.e.
  -- `2 = 1 * 2` and the `.mp` argument is `orderOf .. ∣ 1` after the split --
  -- equivalently Mathlib's `Nat.dvd_prime` here is
  --   `a ∣ b * c -> (a ∣ b ∨ a ∣ c)`.
  -- So the product must be presented as `p ∣ (2) * (m ^ 2)` with the LEFT
  -- factor `2` extracted, and `Nat.dvd_prime hp` applied to that.
  -- `Nat.Prime.dvd_mul` is the declaration that splits a product by a prime;
  -- the accepted corpus uses it in exactly this form at
  -- `solution_even_orders_mod_157_q3_twentythree.lean:32`,
  -- `(Nat.Prime.dvd_mul hr).mp hdiv` with `hdiv : r ∣ 2^3 * 13`.  `Nat.dvd_prime`
  -- is the CORE version and needs the dividend shaped differently, which is why
  -- three earlier attempts were rejected with `expected to have type ?m ∣ p`.
  obtain h2 | hm2 := (Nat.Prime.dvd_mul hp).mp hdvd
  · -- `p ∣ 2` with `p` prime forces `p = 2`.  Candidate 5527 reported
    -- `Invalid field ne_two: The environment does not contain Irreducible.ne_two`,
    -- so `ne_two` is not projected from the primality proof.  The bound route
    -- works instead: `p ∣ 2` gives `p ≤ 2`, primality gives `2 ≤ p`.
    have hpbound : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    have hpmin : 2 ≤ p := hp.two_le
    -- `hp2` is `(p != 2) = true`, i.e. a `decide`-style boolean, so it cannot be
    -- applied directly: candidate 5607 reported `Function expected at hp2`.
    -- `p = 2` contradicts it after the boolean is read as a `Ne`.
    have hne2 : p ≠ 2 := by simpa using hp2
    have hp2' : p = 2 := by omega
    exact hne2 hp2'
  · exact hpm (hp.dvd_of_dvd_pow hm2)

end EulerIdx
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {p m d1 q r : Nat} (hp : p.Prime)
    (hp2 : p != 2) (hpm : Not (Dvd.dvd p m))
    (h1 : 2 * m ^ 2 =
      (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r))) :
    Not (Dvd.dvd p (d1 ^ 2 * (q * r))) :=
  OddPerfectNumber.Kernel.EulerIdx.solution_aux hp hp2 hpm h1
