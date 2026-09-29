-- Prove2me | solution 1 for S_recip_random_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T06:37:37.109408+00:00
-- url     : https://prove2.me/submissions/afd9b76a-b070-489f-876b-0abf5390e99b

import Mathlib
import Definitions.Def_timepiece_corrector
import Theorems.Thm_X_mult_zero
open Complex Finset Filter Topology
open scoped ArithmeticFunction ArithmeticFunction.Moebius ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (N P : ℕ) (s : ℂ) :
    S_recip_random N P s (fun _ ↦ 0) = S_classical N s := by
  unfold S_recip_random S_classical
  exact sum_congr rfl (fun n _ ↦ by rw [X_mult_zero, mul_one])
