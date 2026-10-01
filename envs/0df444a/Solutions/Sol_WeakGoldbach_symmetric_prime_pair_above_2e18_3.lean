-- Prove2me | solution 3 for WeakGoldbach.symmetric_prime_pair_above_2e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T01:50:57.180818+00:00
-- url     : https://prove2.me/submissions/6a02cc75-51fd-437c-8341-8040c33e08ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_symmetric_pair_count_pos_above_2e18

open WeakGoldbach

theorem solution (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    ∃ t : ℕ, t ≤ m - 2 ∧ Nat.Prime (m - t) ∧ Nat.Prime (m + t) := by
  have hcard :
      0 < ((Finset.range (m - 1)).filter
        (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t))).card :=
    WeakGoldbach.symmetric_pair_count_pos_above_2e18 m hm
  -- A positive cardinality of a `Finset ℕ` means the set is inhabited, so it
  -- contains a witness `t`.
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hcard
  -- `Finset.mem_filter` returns the membership in the underlying set first and
  -- the filter predicate second, so the two are destructured in that order:
  -- `htmem` is `t ∈ Finset.range (m - 1)` and `hprim` is the conjunction of
  -- the two primality hypotheses.
  obtain ⟨htmem, hprim⟩ := Finset.mem_filter.mp ht
  refine ⟨t, ?_, hprim.1, hprim.2⟩
  -- `t ∈ range (m - 1)` bounds `t < m - 1`, which for naturals is exactly the
  -- floor `t ≤ m - 2` that the statement declares.
  have htlt : t < m - 1 := Finset.mem_range.mp htmem
  omega
