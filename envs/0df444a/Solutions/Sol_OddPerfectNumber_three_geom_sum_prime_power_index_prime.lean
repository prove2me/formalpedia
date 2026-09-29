-- Prove2me | solution 1 for OddPerfectNumber.three_geom_sum_prime_power_index_prime
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-21T01:01:33.908803+00:00
-- url     : https://prove2.me/submissions/04cea82c-62b4-4540-92ca-4b1c799c8933

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

theorem solution : ¬ (∀ (b t r beta : Nat), 1 < t → Odd t →
    r.Prime → 0 < beta →
    (Finset.range t).sum (fun i => b ^ i) = r ^ beta → t.Prime) := by
  intro h
  have hbad := h 1 9 3 2 (by norm_num) (by decide) (by decide)
    (by norm_num) (by norm_num)
  exact (by decide : ¬ Nat.Prime 9) hbad

#print axioms solution
