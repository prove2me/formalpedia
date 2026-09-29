-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_floor_envelope_low
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T05:20:02.180834+00:00
-- url     : https://prove2.me/submissions/98fab0bb-93f9-42e9-a371-f7e23fdce42f

import Mathlib
import Mathlib.NumberTheory.Chebyshev

theorem solution (t : Real) (h1 : 1420 <= t) (h2 : t <= 10 ^ 4) :
    t * (1 - 1 / (2 * Real.log t)) <=
      ((Nat.floor t : Real) + 1) * (1 - 1 / (2 * Real.log ((Nat.floor t : Real) + 1))) := by
  have htb : t ≤ (Nat.floor t : Real) + 1 := (Nat.lt_floor_add_one t).le
  have ht0 : 0 < t := by linarith
  have hinv : t⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ ht0 (by norm_num)]
    norm_num
    linarith
  have hlog_half : 1 / 2 ≤ Real.log t := by
    have := Real.one_sub_inv_le_log_of_pos ht0
    linarith
  have hLa : 0 < Real.log t := by linarith
  have hLb : Real.log t ≤ Real.log ((Nat.floor t : Real) + 1) := Real.log_le_log ht0 htb
  have hb0 : 0 ≤ (Nat.floor t : Real) + 1 := by linarith
  have key1 : ((Nat.floor t : Real) + 1) / (2 * Real.log ((Nat.floor t : Real) + 1)) ≤
      ((Nat.floor t : Real) + 1) / (2 * Real.log t) :=
    div_le_div_of_nonneg_left hb0 (by positivity) (by linarith)
  have key2 : ((Nat.floor t : Real) + 1 - t) / (2 * Real.log t) ≤ (Nat.floor t : Real) + 1 - t := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have e1 : t * (1 - 1 / (2 * Real.log t)) = t - t / (2 * Real.log t) := by ring
  have e2 : ((Nat.floor t : Real) + 1) * (1 - 1 / (2 * Real.log ((Nat.floor t : Real) + 1))) =
      ((Nat.floor t : Real) + 1) - ((Nat.floor t : Real) + 1) / (2 * Real.log ((Nat.floor t : Real) + 1)) := by ring
  have e3 : ((Nat.floor t : Real) + 1 - t) / (2 * Real.log t) =
      ((Nat.floor t : Real) + 1) / (2 * Real.log t) - t / (2 * Real.log t) := by ring
  rw [e1, e2]
  linarith

#print axioms solution
