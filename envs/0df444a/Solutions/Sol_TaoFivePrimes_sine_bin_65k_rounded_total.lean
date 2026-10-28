-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_rounded_total
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:57:18.907049+00:00
-- url     : https://prove2.me/submissions/5f786887-625f-40d8-8c8e-8be229acf1b0

import Definitions.Def_TaoFivePrimes_SineBinArithmetic65k
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

theorem solution :
    (∑ i ∈ Finset.range 180, (TaoFivePrimes.sineBinTerm65k i:ℝ)/10^21) +
      (81609874820:ℝ)/10^21 ≤ (115/10^11:ℝ) := by
  norm_num (config := {maxSteps := 1000000}) [Finset.sum_range_succ, TaoFivePrimes.sineBinTerm65k]
