-- Prove2me | solution 1 for WeakGoldbach.verified_range_explicit_sieve_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:33:23.05067+00:00
-- url     : https://prove2.me/submissions/27b11431-6799-4294-ae3f-2a2259718905
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_WeakGoldbach_verified_range_pointwise_sieve_coverage

set_option autoImplicit false

open GoldbachSieve

/-- Unfolding `GoldbachSieve.survivors` recovers the explicit finite-filter
certificate from the pointwise survivor formulation. -/
theorem solution (n : Nat)
    (hlo : Nat.le (4 * 10 ^ 14) n) (hhi : Nat.le n (4 * 10 ^ 18)) (heven : Even n) :
    Exists fun p : Nat => Exists fun q : Nat =>
      And (Nat.Prime p) (And (Nat.le p 9781)
        (And (Membership.mem (Finset.Icc (max 2 (n - 9781)) n) q)
          (And (p + q = n)
            ((((Finset.Icc 2 2000000000).filter Nat.Prime).filter
              (fun r => And (Dvd.dvd r q) (Not (r = q)))) =
                (Finset.empty : Finset Nat))))) := by
  obtain ⟨p, q, hp, hpbound, hqsurv, hpq⟩ :=
    WeakGoldbach.verified_range_pointwise_sieve_coverage n hlo hhi heven
  refine ⟨p, q, hp, hpbound, ?_, hpq, ?_⟩
  · -- survivors live in `Icc (max 2 lo) hi`
    have hqmem := (Finset.mem_filter.mp hqsurv).1
    simpa [survivors] using hqmem
  · -- the filtered prime set has card 0, hence is empty
    have hcard : ((((Finset.Icc 2 2000000000).filter Nat.Prime).filter
        (fun r => r ∣ q ∧ r ≠ q)).card = 0) := by
      have := (Finset.mem_filter.mp hqsurv).2
      -- survivors filters with the same primes/cutoff
      simpa [survivors] using this
    exact Finset.card_eq_zero.mp hcard
