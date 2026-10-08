-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_two_prime_index_three_exponent_one_gives_thirteen_dvd_d1_given_index_primes_ne_thirteen
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T15:39:04.104988+00:00
-- url     : https://prove2.me/submissions/ff16b1b6-2ef4-4d51-b544-07064380ed3a

-- Target: OddPerfectNumber.Kernel
--   .five_two_prime_index_three_exponent_one_gives_thirteen_dvd_d1_given_index_primes_ne_thirteen
--         (689ded24-ec3c-4274-9ef3-b2f5c011c503)
--
-- REPAIR of 6911 (v37).  11 groups read from ONE verified 556-line capture;
-- declared=11 captured=11, END OF CE REPORT groups=11 diagnostics=11, exit 0.
--
-- THE DECISIVE API FACT, verified in the pinned revision
-- (Mathlib/Data/Nat/Prime/Defs.lean:188):
--
--   Nat.prime_dvd_prime_iff_eq {p q} (pp : p.Prime) (qp : q.Prime) : p ∣ q ↔ p = q
--
-- v37 used `Nat.dvd_prime h13` whose actual signature (Defs.lean:181) is
--
--   Nat.dvd_prime {p m} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m = p
--
-- i.e. the SUBJECT is the divisor and the conclusion carries a spurious
-- `m = 1` disjunct.  Because Lean must pick the implicit `m`, the compiler
-- reported `expected to have type ?m ∣ 13` against the supplied `13 ∣ p` --
-- six times (lines 51, 56, 61, 68, 76, 79).  `prime_dvd_prime_iff_eq` has the
-- SAME subject order as what v37 actually had, but the clean conclusion `p = q`
-- with no `= 1` disjunct, so all six failures collapse into one rewrite.
--
-- E01 L25 `introN` failed: the goal there is the BOOLEAN `(m != 0) = true`,
-- not a Prop.  v37 wrote `have hm0 : m != 0 := by intro hmz; ...`, but `!=` is
-- `bne`, so the binder is already consumed.  Fixed by declaring `hm0` as a Prop
-- via the accepted mission idiom `bne_iff_ne.mp`, exactly as in
-- kernel5_20260928/05_FiveSigmaPrime.lean:34 and the ACCEPTED work/opn/v20.
--
-- E02 L31 `Nat.mem_primeFactors` is a pair, not `And.intro h3dvd`; its second
-- component is `Nat.Prime 3`, which must be supplied explicitly.
--
-- E03-E08 L72/L74/L76/L82: `13 ∣ d1 ^ 2` does NOT mean `(13 ∣ d1) ^ 2` -- that
-- is the Prop-power notation, hence the `HPow Prop` failure at L72.  Euclid must
-- be peeled properly: `Nat.Prime.dvd_of_dvd_pow` (Basic.lean:153) turns
-- `13 ∣ d1 ^ 2` into `13 ∣ d1` directly.  E09 was a cascade of E03.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_local_sigma_dvd_sigma_of_mem_primeFactors

open OddPerfectNumber.Kernel

theorem solution (p m d1 q r : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hm : Odd m) (hpm : Not (Dvd.dvd p m)) (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (hq3 : q != 3) (hr3 : r != 3) (hp13 : p != 13) (hq13 : q != 13) (hr13 : r != 13)
    (he : m.factorization 3 = 1)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    Dvd.dvd 13 d1 := by
  have h13 : (13 : Nat).Prime := by norm_num
  have h3 : (3 : Nat).Prime := by norm_num
  -- E01 repair, and a second real defect fixed at the same time: 6921's line-56
  -- `omega` failure came from `omega` ingesting EVERY hypothesis, including
  -- `hp4 : p % 4 = 1`, whose counterexample terms (`a := ↑p / 4`) appear in the
  -- model.  `omega` is never needed here: the goal after `intro` is `False` and
  -- the contradiction is arithmetic in `0.factorization 3 = 1`, so it is closed
  -- by `norm_num`/`simp` alone.
  have hm0 : m ≠ 0 := by
    intro hmz
    rw [hmz, Nat.factorization_zero] at he
    norm_num at he
  -- E02 repair, with the EXACT component order verified in the pinned revision
  -- (Mathlib/Data/Nat/PrimeFin.lean:41):
  --   Nat.mem_primeFactors : p ∈ n.primeFactors ↔ p.Prime ∧ p ∣ n ∧ n ≠ 0
  -- so the components are (Prime, dvd, ne_zero) -- which is why v37's
  -- `And.intro h3dvd` failed with `expected to have type Nat.Prime 3`.
  have h3dvd : Dvd.dvd 3 m := Nat.dvd_of_factorization_pos (by rw [he]; norm_num)
  have hmem : (3 : Nat) ∈ m.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨h3, h3dvd, hm0⟩
  -- The child's FIRST argument is the BOOLEAN `(n != 0)`, not the Prop `n != 0`;
  -- its exact authoritative signature is
  --   local_sigma_dvd_sigma_of_mem_primeFactors {n l} (hn : n != 0) (hl : l ∈ n.primeFactors)
  have hm0b : m != 0 := by
    rw [bne_iff_ne]
    exact hm0
  have hloc : Dvd.dvd (∑ i ∈ Finset.range (2 * m.factorization 3 + 1), (3 : Nat) ^ i)
      (∑ d ∈ (m ^ 2).divisors, d) := local_sigma_dvd_sigma_of_mem_primeFactors hm0b hmem
  have hgeom : (∑ i ∈ Finset.range (2 * m.factorization 3 + 1), (3 : Nat) ^ i) = 13 := by
    rw [he]
    decide
  have h13sigma : Dvd.dvd 13 (∑ d ∈ (m ^ 2).divisors, d) := by
    rw [← hgeom]
    exact hloc
  have h13prod : Dvd.dvd 13 (p ^ 5 * (d1 ^ 2 * (q * r))) := by
    rw [← h2]
    exact h13sigma
  -- E03-E08 repair: `prime_dvd_prime_iff_eq : p ∣ q ↔ p = q` has the exact
  -- subject order used here and no `= 1` disjunct, so each exclusion is one
  -- rewrite of the BOOLEAN hypothesis followed by the propositional inequality.
  have hp13n : p ≠ 13 := bne_iff_ne.mp hp13
  have hq13n : q ≠ 13 := bne_iff_ne.mp hq13
  have hr13n : r ≠ 13 := bne_iff_ne.mp hr13
  have hp13' : ¬ (13 : Nat) ∣ p := fun h => hp13n ((Nat.prime_dvd_prime_iff_eq h13 hp).mp h).symm
  have hq13' : ¬ (13 : Nat) ∣ q := fun h => hq13n ((Nat.prime_dvd_prime_iff_eq h13 hq).mp h).symm
  have hr13' : ¬ (13 : Nat) ∣ r := fun h => hr13n ((Nat.prime_dvd_prime_iff_eq h13 hr).mp h).symm
  -- Euclid, peeled in the goal's own nesting
  have hstep1 : Dvd.dvd 13 (d1 ^ 2 * (q * r)) := by
    rcases h13.dvd_mul.mp h13prod with hP | hB
    · exact absurd (h13.dvd_of_dvd_pow hP) hp13'
    · exact hB
  -- E03-E08 repair: `Dvd.dvd 13 d1 ^ 2` PARSES as `(13 | d1) ^ 2`, because `^`
  -- binds tighter than the infix `|`.  That is why 6921 reported
  -- `failed to synthesize instance of type class HPow Prop Nat Prop` at the
  -- declaration line and then `Unknown identifier hstep2` downstream.  The
  -- parentheses below make the intended reading `13 | (d1 ^ 2)` explicit.
  have hstep2 : Dvd.dvd 13 (d1 ^ 2) := by
    rcases h13.dvd_mul.mp hstep1 with hD | hQR
    · exact hD
    · rcases h13.dvd_mul.mp hQR with hQ | hR
      · exact absurd hQ hq13'
      · exact absurd hR hr13'
  exact h13.dvd_of_dvd_pow hstep2

