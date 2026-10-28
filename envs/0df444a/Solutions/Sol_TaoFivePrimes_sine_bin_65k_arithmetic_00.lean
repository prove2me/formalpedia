-- Prove2me | solution 1 for TaoFivePrimes.sine_bin_65k_arithmetic_00
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:57:19.015799+00:00
-- url     : https://prove2.me/submissions/599b0482-0442-4deb-b8d5-266e5a7af547

import Definitions.Def_TaoFivePrimes_SineBinData65k
import Definitions.Def_TaoFivePrimes_SineBinArithmetic65k
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

theorem solution (i : Fin 60) :
    (2*(TaoFivePrimes.sineBinCount65k (i.val+0):ℝ)*
      (4*(TaoFivePrimes.sineBinNumerator65k (i.val+0):ℝ)/10000 + 8/2149 +
        3*(65000+1290*((i.val:ℝ)+0+1))/2149^2))/
          (65000+1290*((i.val:ℝ)+0))^3 ≤
      (TaoFivePrimes.sineBinTerm65k (i.val+0):ℝ)/10^21 := by
  fin_cases i <;> norm_num [TaoFivePrimes.sineBinCount65k,
    TaoFivePrimes.sineBinNumerator65k, TaoFivePrimes.sineBinTerm65k]
