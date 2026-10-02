-- Prove2me | solution 2 for WeakGoldbach.three_odd_primes_ge_exp3100
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T08:38:42.875373+00:00
-- url     : https://prove2.me/submissions/74c1dfe7-2b2f-41bd-b3f3-0f5b77fc3736
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd_ge_9

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

-- Reduction of `three_odd_primes_ge_exp3100` through the CORRECTED floor-9
-- all-odd record `ternary_goldbach_all_odd_ge_9` (42fb8198, Open).
--
-- Defect being retired: this target's only registered decomposition child is
-- `ternary_goldbach_all_odd` (4e160e92), which is DISPROVED. It is refuted at
-- n = 7, where the only three-prime decomposition is 7 = 2 + 2 + 3, which is
-- not all-odd. But this target's own hypothesis `exp 3100 <= n` already implies
-- `9 <= n`, so the refuting value is excluded by the target's own range and the
-- edge is semantically wrong rather than merely stale. This candidate imports
-- the non-refuted floor-9 statement instead, which is the same proposition the
-- target actually needs.
open WeakGoldbach

theorem solution (n : ℕ) (hn : Real.exp 3100 ≤ (n : ℝ)) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  -- The target's own range hypothesis already supplies the floor the corrected
  -- floor-9 child needs: `exp 3100 >= 9`.
  --
  -- `Real.add_one_le_exp 8` is exactly `9 <= exp 8`, and `Real.exp_le_exp` is the
  -- monotonicity step `exp 8 <= exp 3100`, provable because `8 <= 3100`. So this
  -- never asks `norm_num` or `linarith` to evaluate a `Real.exp` atom, which is
  -- what defeated the earlier variants: `exp` is transcendental and has no
  -- closed form, so no numeric normaliser can reduce it.
  --
  -- Every step is a `calc` with both endpoints written out, because the previous
  -- version left the `le_trans` intermediate type to elaboration and Lean
  -- reported the residual `⊢ 8 ≤ ?m.50`. It also used `Nat.cast_le.mp` as a
  -- rewrite argument, but `Nat.cast_le` is an `↔`, not an equation, so the
  -- rewrite was rejected; here it is applied as a term instead.
  have hlo : 9 ≤ n := by
    have hexp : (9 : ℝ) ≤ Real.exp 3100 := by
      calc (9 : ℝ) = 8 + 1 := by norm_num
        _ ≤ Real.exp 8 := Real.add_one_le_exp 8
        _ ≤ Real.exp 3100 := (Real.exp_le_exp).mpr (by norm_num)
    exact (Nat.cast_le (α := ℝ)).mp (hexp.trans hn)
  obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
    WeakGoldbach.ternary_goldbach_all_odd_ge_9 n hlo hodd
  exact ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩
