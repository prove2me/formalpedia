-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_arithmetic_02
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:57:19.316845+00:00
-- url     : https://prove2.me/submissions/55589df2-b2a9-4f8e-a7e5-bf4268cc306b

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Definitions.Def_TaoFivePrimes_SineBinArithmetic65k
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

theorem solution (i : Fin 60) :
    (2*(TaoFivePrimes.sineBinCount65k (i.val+120):ℝ)*
      (4*(TaoFivePrimes.sineBinNumerator65k (i.val+120):ℝ)/10000 + 8/2149 +
        3*(65000+1290*((i.val:ℝ)+120+1))/2149^2))/
          (65000+1290*((i.val:ℝ)+120))^3 ≤
      (TaoFivePrimes.sineBinTerm65k (i.val+120):ℝ)/10^21 := by
  fin_cases i <;> norm_num [TaoFivePrimes.sineBinCount65k,
    TaoFivePrimes.sineBinNumerator65k, TaoFivePrimes.sineBinTerm65k]
