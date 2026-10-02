-- Prove2me | solution 2 for WeakGoldbach.verified_range_pointwise_sieve_coverage
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T16:02:56.87588+00:00
-- url     : https://prove2.me/submissions/c3895701-ac75-4eb5-bbf5-0c24a270004c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Theorems.Thm_WeakGoldbach_verified_range_explicit_sieve_certificate
import Mathlib

set_option maxHeartbeats 400000

open WeakGoldbach

theorem solution (n : Nat)
    (hlo : Nat.le (4 * 10 ^ 14) n) (hhi : Nat.le n (4 * 10 ^ 18)) (heven : Even n) :
    Exists fun p : Nat => Exists fun q : Nat =>
      And (Nat.Prime p) (And (Nat.le p 9781)
        (And (Membership.mem (GoldbachSieve.survivors (n - 9781) n 2000000000) q) (p + q = n))) := by
  obtain ⟨p, q, hp, hp9781, hqmem, hpq, hsieve⟩ :=
    verified_range_explicit_sieve_certificate n hlo hhi heven
  refine ⟨p, q, hp, hp9781, ?_, hpq⟩
  rw [GoldbachSieve.survivors]
  exact Finset.mem_filter.mpr ⟨hqmem, by
    rw [Finset.card_eq_zero]
    exact hsieve⟩
