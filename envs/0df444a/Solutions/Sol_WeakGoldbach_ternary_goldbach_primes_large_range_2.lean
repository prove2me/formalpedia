-- Prove2me | solution 2 for WeakGoldbach.ternary_goldbach_primes_large_range
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T11:45:12.465001+00:00
-- url     : https://prove2.me/submissions/c2e7d67b-f51d-4412-9f0c-eba6dcb7946c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd_ge_9

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

-- Repair of candidate 6274 (CE, 3 groups, all UNKNOWN_IDENTIFIER).
--
-- ACCOUNTING OF THE CE's THREE INDEPENDENT GROUPS (captured report
-- /tmp/p2m-ce-6274.Nj7dwS, complete=YES, 3 groups / 3 diagnostics, marker
-- candidate=6274 groups=3 diagnostics=3):
--
--   E01  L30  UNKNOWN IDENTIFIER  Nat.Prime.odd_of_gt_two  -> REPAIRED
--   E02  L31  UNKNOWN IDENTIFIER  Nat.Prime.odd_of_gt_two  -> REPAIRED
--   E03  L32  UNKNOWN IDENTIFIER  Nat.Prime.odd_of_gt_two  -> REPAIRED
--
-- All three groups name ONE root cause: the declaration
-- `Nat.Prime.odd_of_gt_two` does not exist in the environment. They are three
-- occurrences of a single mistake, not three independent faults, but each
-- occurrence is repaired independently below.
--
-- RESOLUTION AGAINST AUTHORITATIVE SOURCE. At the pinned revision
-- 0df444a360ea, Mathlib/Data/Nat/Prime/Basic.lean:99-103 provides:
--
--   theorem Prime.odd_iff      {p : ℕ} (hp : Prime p) : Odd p ↔ 3 ≤ p
--   theorem Prime.odd_of_ne_two {p : ℕ} (hp : p.Prime) (h_two : p ≠ 2) : Odd p
--
-- confirmed by the revision-keyed declaration index:
--   Nat.Prime.odd_iff        Mathlib/Data/Nat/Prime/Basic.lean:99
--   Nat.Prime.odd_of_ne_two  Mathlib/Data/Nat/Prime/Basic.lean:103
-- No declaration ending in `odd_of_gt_two` exists.
--
-- DIRECTION NOTE, which is the part the previous attempt had backwards.
-- The target's hypothesis is `Odd p` and the goal is `2 < p`, so the
-- implication needed is `Odd p -> 2 < p`. Both available lemmas run the other
-- way (`Prime p` plus a `≠ 2` side condition gives `Odd p`), so neither can be
-- applied as a projection `.mpr`. The correct tool is the same equivalence read
-- backwards, which is a direct application of `hp.odd_iff.mp hop`:
--
--   hp.odd_iff : Odd p ↔ 3 ≤ p        so   hp.odd_iff.mp hop : 3 ≤ p
--
-- `Nat.Prime.odd_iff` states exactly `Odd p ↔ 3 ≤ p`, and `3 ≤ p` immediately
-- gives `2 < p`. The earlier code also named the lemma wrongly, so it failed on
-- the name before the direction could even be tested; both faults are fixed by
-- the single replacement `exact hp.odd_iff.mp hop` (plus `omega`/`exact`).
--
-- UNCHANGED FROM 6274 AND ALREADY REMOTE-VERIFIED AS FAR AS IT GOES: the
-- rational floor step `9 <= exp 3100` via `Real.add_one_le_exp 3100`, the
-- transport to `9 <= n`, and the application of the corrected floor-9 child.
-- The child import and the floor arithmetic produced no error group in the
-- report, so they are carried across unchanged rather than rewritten.
open WeakGoldbach

theorem solution (n : Nat) (hodd : Odd n) (hlo : Real.exp 3100 <= (n : Real)) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (2 < p) (And (2 < q) (And (2 < r) (n = p + q + r)))))) := by
  -- Rational floor step, carried across from 6274: `exp x >= 1 + x` at
  -- `x = 3100` is closed rational arithmetic, so no transcendental atom is ever
  -- asked to reduce. `linarith` disposes of `1 + 3100 >= 9` outright.
  have hexp : (9 : Real) <= Real.exp 3100 := by
    have h := Real.add_one_le_exp 3100
    linarith
  have h9 : 9 <= n := Nat.le_trans (Nat.cast_le.mp (hexp.trans hlo)) (by norm_num)
  -- The corrected floor-9 child covers every odd `n >= 9` with no upper bound,
  -- so this target's asymptotic hypothesis is exactly what it needs.
  obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
    WeakGoldbach.ternary_goldbach_all_odd_ge_9 n h9 hodd
  refine ⟨p, q, r, hp, hq, hr, ?_, ?_, ?_, hsum⟩
  -- REPAIRS of E01/E02/E03. `Nat.Prime.odd_iff : Odd p ↔ 3 ≤ p` is read in the
  -- `Odd p -> 3 ≤ p` direction, which is the one this goal actually needs, and
  -- `3 ≤ p` yields `2 < p` with no further hypothesis.
  · exact hp.odd_iff.mp hop
  · exact hq.odd_iff.mp hoq
  · exact hr.odd_iff.mp hor
